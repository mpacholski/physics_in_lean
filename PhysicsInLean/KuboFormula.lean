import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Part I: The Interaction Picture and the Kubo Linear Response Formula

This file formalizes the operator calculus underlying linear response theory on an
arbitrary complex Hilbert space `ℋ`:

1. **Unperturbed Evolution (`U₀`)**: Defined via the Banach-algebra exponential
   `U₀(t) = exp(t • (-i H₀))` on continuous linear operators `ℋ →L[ℂ] ℋ`.
2. **The Interaction Picture (`Ψ_I`, `V_I`, `A_I`)**: Transforming states and
   observables by `U₀(-t)` cancels the free drift `H₀`, leaving the interaction
   Schrödinger equation `dΨ_I/dt = -i V_I(t) Ψ_I(t)` (`satisfiesInteractionSchrodinger`).
3. **First-Order Perturbation & Kubo Commutator (`kubo_commutator_identity`)**:
   Differentiating with respect to the coupling strength at `g = 0` and using the
   conjugate-linearity of the inner product in the bra argument yields the
   expectation value of the commutator `-i ⟪ψ₀, [A_I(t), V_I(s)] ψ₀⟫`.
4. **Frequency-Space Lehmann / Lindhard Poles (`lindhard_two_pole_formula`)**:
   Driving a transition of Bohr energy `ΔE` at complex frequency `z = ω + iη`
   produces the resonant `1 / (z - ΔE)` and anti-resonant `- 1 / (z + ΔE)` poles.
-/

open Complex InnerProductSpace

noncomputable section

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- Local notation `⟪x, y⟫` for the complex inner product on `ℋ`
    (conjugate-linear in `x`, linear in `y`). -/
local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-! ### 1. Definitions of the Schrödinger and Interaction Pictures -/

/- Time-dependent state trajectory in the Schrödinger picture. -/
variable (Ψ_S : ℂ → ℋ)

/- Unperturbed time-independent Hamiltonian `H₀` and time-dependent perturbation `V(t)`. -/
variable (H₀ : ℋ →L[ℂ] ℋ) (V : ℂ → ℋ →L[ℂ] ℋ)

/-- Free time-evolution operator `U₀(t) = exp(-i H₀ t)` in the Banach algebra `ℋ →L[ℂ] ℋ`. -/
def U₀ (t : ℂ) : ℋ →L[ℂ] ℋ :=
  NormedSpace.exp (t • ((-I) • H₀))

/-- State vector in the Interaction picture: `Ψ_I(t) = U₀(-t) Ψ_S(t)`. -/
def Ψ_I (t : ℂ) : ℋ :=
  U₀ H₀ (-t) (Ψ_S t)

/-- Perturbation operator in the Interaction picture: `V_I(t) = U₀(-t) V(t) U₀(t)`. -/
def V_I (t : ℂ) : ℋ →L[ℂ] ℋ :=
  (U₀ H₀ (-t)).comp ((V t).comp (U₀ H₀ t))

/-- Any bounded observable `A` in the Interaction picture: `A_I(t) = U₀(-t) A U₀(t)`. -/
def A_I (A : ℋ →L[ℂ] ℋ) (t : ℂ) : ℋ →L[ℂ] ℋ :=
  (U₀ H₀ (-t)).comp (A.comp (U₀ H₀ t))

/-- Commutator of two continuous linear operators: `[X, Y] = X Y - Y X`. -/
def clmCommutator (X Y : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ :=
  X.comp Y - Y.comp X

/-! ### 2. Group Property and Time Derivatives of Free Evolution `U₀(t)` -/

/-- Forward and backward free evolution cancel: `U₀(t) (U₀(-t) ψ) = ψ`. -/
lemma U₀_mul_U₀_neg (t : ℂ) (ψ : ℋ) :
    U₀ H₀ t (U₀ H₀ (-t) ψ) = ψ := by
  let : NormedAlgebra ℚ (ℋ →L[ℂ] ℋ) := NormedAlgebra.restrictScalars ℚ ℂ _
  change ((U₀ H₀ t) * (U₀ H₀ (-t))) ψ = ψ
  dsimp [U₀]
  have h_comm : Commute (t • ((-I) • H₀)) ((-t) • ((-I) • H₀)) :=
    (Commute.refl ((-I) • H₀)).smul_left t |>.smul_right (-t)
  rw [← NormedSpace.exp_add_of_commute h_comm]
  simp

/-- Time derivative of the forward evolution operator `U₀(t)` is `-i U₀(t) H₀`. -/
lemma hasDerivAt_U₀ (t : ℂ) :
    HasDerivAt (U₀ H₀) ((-I) • (U₀ H₀ t).comp H₀) t := by
  have h : HasDerivAt (U₀ H₀) (U₀ H₀ t * ((-I) • H₀)) t :=
    hasDerivAt_exp_smul_const ((-I) • H₀) t
  simpa [ContinuousLinearMap.mul_def] using h

/-- By the chain rule (`s ↦ -s`), the time derivative of `U₀(-t)` is `+i U₀(-t) H₀`. -/
lemma hasDerivAt_U₀_neg (t : ℂ) :
    HasDerivAt (fun s : ℂ ↦ U₀ H₀ (-s)) (I • (U₀ H₀ (-t)).comp H₀) t := by
  have h_chain := HasDerivAt.scomp t (hasDerivAt_U₀ H₀ (-t)) (hasDerivAt_neg t)
  simpa [neg_smul, smul_neg, Function.comp_def] using h_chain

/-! ### 3. The Interaction Picture Equation of Motion -/

/-- **Interaction Picture Theorem**:
    If `Ψ_S(t)` satisfies the Schrödinger equation `dΨ_S/dt = -i (H₀ + V(t)) Ψ_S(t)`,
    then in the Interaction picture the `H₀` drift cancels out and `Ψ_I(t)` satisfies
    `dΨ_I/dt = -i V_I(t) Ψ_I(t)`. -/
theorem satisfiesInteractionSchrodinger
    (satisfiesSchrodinger : ∀ t : ℂ, HasDerivAt Ψ_S ((-I) • (H₀ (Ψ_S t) + V t (Ψ_S t))) t)
    (t : ℂ) :
    HasDerivAt (Ψ_I Ψ_S H₀) ((-I) • (V_I H₀ V t (Ψ_I Ψ_S H₀ t))) t := by
  have h_deriv := HasDerivAt.clm_apply (hasDerivAt_U₀_neg H₀ t) (satisfiesSchrodinger t)
  convert h_deriv
  · simp [Ψ_I]
  · simp [V_I, Ψ_I, ContinuousLinearMap.comp_apply, U₀_mul_U₀_neg]

/-! ### 4. First-Order Perturbation and the Kubo Commutator Identity -/

/-- Differentiating the interaction generator `-i (g • V_I(t)) (Φ g)` with respect to the
    coupling constant `g` at `g = 0` isolates the first-order source `-i V_I(t) ψ₀`. -/
lemma hasDerivAt_perturbation_zero
    (ψ₀ δΦ : ℋ) (Φ : ℂ → ℋ)
    (hΦ_zero : Φ 0 = ψ₀)
    (hΦ_deriv : HasDerivAt Φ δΦ 0)
    (t : ℂ) :
    HasDerivAt (fun g : ℂ ↦ (-I) • (g • V_I H₀ V t) (Φ g))
      ((-I) • (V_I H₀ V t ψ₀)) 0 := by
  have hV_g : HasDerivAt (fun g : ℂ ↦ g • V_I H₀ V t) (V_I H₀ V t) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const (V_I H₀ V t)
  have h_prod := (hV_g.clm_apply hΦ_deriv).const_smul (-I)
  convert h_prod using 1
  simp [hΦ_zero]

/-- **The Kubo Commutator Identity**:
    For a first-order state variation `δψ = (-i) • V_I(s) ψ₀` and a self-adjoint
    perturbation `V_I(s)`, the linear variation of the expectation value of `A_I(t)`
    equals `-i ⟪ψ₀, [A_I(t), V_I(s)] ψ₀⟫`. -/
theorem kubo_commutator_identity
    (A : ℋ →L[ℂ] ℋ) (ψ₀ : ℋ) (t s : ℂ)
    (hV_sa : ∀ x y : ℋ, ⟪V_I H₀ V s x, y⟫ = ⟪x, V_I H₀ V s y⟫) :
    let δψ := (-I) • (V_I H₀ V s ψ₀)
    ⟪δψ, A_I H₀ A t ψ₀⟫ + ⟪ψ₀, A_I H₀ A t δψ⟫ =
      (-I) * ⟪ψ₀, clmCommutator (A_I H₀ A t) (V_I H₀ V s) ψ₀⟫ := by
  intro δψ
  dsimp [δψ, clmCommutator]
  rw [inner_smul_left, map_smul, inner_smul_right, hV_sa ψ₀ (A_I H₀ A t ψ₀)]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, inner_sub_right]
  simp
  ring

/-! ### 5. Adiabatic Frequency Switching and the Two-Pole Lehmann / Lindhard Formula -/

/-- **Adiabatic Frequency Antiderivative**:
    For any complex driving frequency `z = ω + iη` and Bohr transition energy `ΔE`
    with `z - ΔE ≠ 0`, the exact antiderivative of the interaction-picture
    oscillation `-i exp(t • (-i (z - ΔE)))` is `exp(t • (-i (z - ΔE))) / (z - ΔE)`. -/
lemma hasDerivAt_lindhard_mode (z ΔE t : ℂ) (hz : z - ΔE ≠ 0) :
    HasDerivAt (fun s : ℂ ↦ NormedSpace.exp (s • (-I * (z - ΔE))) / (z - ΔE))
      ((-I) * NormedSpace.exp (t • (-I * (z - ΔE)))) t := by
  have h_exp := (hasDerivAt_exp_smul_const (-I * (z - ΔE)) t).div_const (z - ΔE)
  convert h_exp using 1
  field_simp [hz]

/-- Lifting `hasDerivAt_lindhard_mode` to the Hilbert space `ℋ` via `.smul_const φ`. -/
lemma hasDerivAt_lindhard_state (z ΔE t : ℂ) (φ : ℋ) (hz : z - ΔE ≠ 0) :
    HasDerivAt (fun s : ℂ ↦ (NormedSpace.exp (s • (-I * (z - ΔE))) / (z - ΔE)) • φ)
      (((-I) * NormedSpace.exp (t • (-I * (z - ΔE)))) • φ) t :=
  (hasDerivAt_lindhard_mode z ΔE t hz).smul_const φ

/-- **Lehmann / Lindhard Two-Pole Susceptibility Formula**:
    Evaluating the linear expectation-value variation `⟪δψ_bra, A ψ₀⟫ + ⟪ψ₀, A δψ_ket⟫`
    on the integrated first-order mode amplitudes produces the resonant (`1 / (z - ΔE)`)
    and anti-resonant (`- 1 / (z + ΔE)`) energy denominators. -/
theorem lindhard_two_pole_formula
    (A : ℋ →L[ℂ] ℋ) (ψ₀ φ : ℋ) (z ΔE : ℂ) :
    let δψ_ket := (1 / (z - ΔE)) • φ
    let δψ_bra := (-(1 / (starRingEnd ℂ z + starRingEnd ℂ ΔE))) • φ
    ⟪δψ_bra, A ψ₀⟫ + ⟪ψ₀, A δψ_ket⟫ =
      ⟪ψ₀, A φ⟫ / (z - ΔE) - ⟪φ, A ψ₀⟫ / (z + ΔE) := by
  intro δψ_ket δψ_bra
  dsimp [δψ_ket, δψ_bra]
  rw [map_smul, inner_smul_right, inner_smul_left]
  simp [div_eq_mul_inv]
  ring

end
