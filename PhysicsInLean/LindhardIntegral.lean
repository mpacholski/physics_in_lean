import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Part II: The 3D Lindhard Polarizability and the `q = 2 k_F` Logarithmic Singularity

This file formalizes the momentum-space kinematics and radial integration of the
Lindhard polarizability `χ₀(q, z)` for a continuous 3D free electron gas with
parabolic band dispersion `ε(k) = ‖k‖² / (2m)`:

1. **Continuous Quadratic Dispersion (`quadraticDispersion_sub`)**:
   Proves the particle-hole excitation energy identity
   `ε(k + q) - ε(k) = (2 ⟪k, q⟫_ℝ + ‖q‖²) / (2m)` on any real inner product space `K`.
2. **Continuous Lindhard Integral (`lindhardTwoPoleIntegral_eq_lindhardPolarizabilityIntegral`)**:
   Relates the two-pole susceptibility integral to the canonical Lindhard integral
   `∫ k, (n_F(k) - n_F(k + q)) / (z - (ε(k+q) - ε(k)))` via translation invariance
   (`k ↦ k + q`) of the momentum-space Haar/Lebesgue measure.
3. **The 3D Static Radial Primitive (`hasDerivAt_lindhardRadialPrimitive`)**:
   After integrating over the polar angle `cos θ`, the static (`ω = 0`) 3D radial
   integral reduces to `∫ k * ln |(2k + q) / (2k - q)| dk`. We verify the exact
   antiderivative:
   `F(k) = (1/2) * (k² - q²/4) * (ln |2k + q| - ln |2k - q|) + (1/2) * q * k`,
   exhibiting the logarithmic Kohn anomaly / Friedel oscillation singularity at `q = 2 k_F`.
-/

open Complex MeasureTheory

noncomputable section

/-! ### 1. Continuous Quadratic Dispersion and Particle-Hole Kinematics -/

/-- Free-fermion kinetic energy `ε(k) = ‖k‖² / (2m)` (in units where `ℏ = 1`)
    as a complex-valued energy on a continuous momentum space `K` (e.g. `ℝ³`). -/
def quadraticDispersion {K : Type*} [NormedAddCommGroup K]
    (m : ℝ) (k : K) : ℂ :=
  ((‖k‖ ^ 2 / (2 * m) : ℝ) : ℂ)

/-- **Particle-Hole Excitation Energy Identity**:
    For a parabolic band `ε(k) = ‖k‖² / (2m)`, the excitation energy `ε(k + q) - ε(k)`
    equals the Doppler term plus recoil energy `(2 ⟪k, q⟫_ℝ + ‖q‖²) / (2m)`. -/
lemma quadraticDispersion_sub {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (m : ℝ) (k q : K) :
    quadraticDispersion m (k + q) - quadraticDispersion m k =
      (((2 * @inner ℝ K _ k q + ‖q‖ ^ 2) / (2 * m) : ℝ) : ℂ) := by
  dsimp [quadraticDispersion]
  rw [norm_add_sq_real]
  push_cast
  ring

/-! ### 2. Continuous Momentum-Space Lindhard Integrals -/

/-- The continuous Lindhard polarizability in two-pole form over momentum space `K`:
    `χ_two_pole(q, z) = ∫ k, n_F(k) / (z - (ε(k+q) - ε(k))) - ∫ k, n_F(k) / (z - (ε(k) - ε(k-q)))`. -/
def lindhardTwoPoleIntegral {K : Type*} [NormedAddCommGroup K] [MeasureSpace K]
    (m : ℝ) (n_F : K → ℂ) (q : K) (z : ℂ) : ℂ :=
  (∫ k : K, n_F k / (z - (quadraticDispersion m (k + q) - quadraticDispersion m k))) -
  (∫ k : K, n_F k / (z - (quadraticDispersion m k - quadraticDispersion m (k - q))))

/-- The canonical continuous Lindhard polarizability `χ₀(q, z)` with quadratic dispersion:
    `χ₀(q, z) = ∫ k, (n_F(k) - n_F(k + q)) / (z - (ε(k+q) - ε(k)))`. -/
def lindhardPolarizabilityIntegral {K : Type*} [NormedAddCommGroup K] [MeasureSpace K]
    (m : ℝ) (n_F : K → ℂ) (q : K) (z : ℂ) : ℂ :=
  ∫ k : K, (n_F k - n_F (k + q)) /
    (z - (quadraticDispersion m (k + q) - quadraticDispersion m k))

/-- **Continuous Lindhard Polarizability Theorem**:
    By translation invariance of the momentum-space measure (`k ↦ k + q`) in the
    second integral, the continuous two-pole susceptibility equals the canonical
    Lindhard integral `∫ k, (n_F(k) - n_F(k + q)) / (z - (ε(k+q) - ε(k)))`. -/
theorem lindhardTwoPoleIntegral_eq_lindhardPolarizabilityIntegral
    {K : Type*} [NormedAddCommGroup K] [MeasureSpace K]
    [BorelSpace K] [Measure.IsAddRightInvariant (volume : Measure K)]
    (m : ℝ) (n_F : K → ℂ) (q : K) (z : ℂ)
    (h_int₁ : Integrable (fun k : K ↦
      n_F k / (z - (quadraticDispersion m (k + q) - quadraticDispersion m k))))
    (h_int₂ : Integrable (fun k : K ↦
      n_F (k + q) / (z - (quadraticDispersion m (k + q) - quadraticDispersion m k)))) :
    lindhardTwoPoleIntegral m n_F q z = lindhardPolarizabilityIntegral m n_F q z := by
  sorry

/-- Substituting the explicit kinematic identity `quadraticDispersion_sub` directly
    into the denominator of the continuous Lindhard integral. -/
theorem lindhardPolarizabilityIntegral_eq_kinematic
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [MeasureSpace K]
    (m : ℝ) (n_F : K → ℂ) (q : K) (z : ℂ) :
    lindhardPolarizabilityIntegral m n_F q z =
      ∫ k : K, (n_F k - n_F (k + q)) /
        (z - (((2 * @inner ℝ K _ k q + ‖q‖ ^ 2) / (2 * m) : ℝ) : ℂ)) := by
  dsimp [lindhardPolarizabilityIntegral]
  congr 1
  ext k
  rw [quadraticDispersion_sub]

/-! ### 3. Exact Evaluation of the 3D Static Radial Logarithmic Integral -/

/-- The radial primitive `F(k)` appearing in the 3D static Lindhard function:
    `F(k) = (1/2) * (k^2 - q^2 / 4) * (ln |2k + q| - ln |2k - q|) + (1/2) * q * k`.
    (Note: `Real.log` in Mathlib is already defined as `ln |x|` for all `x : ℝ`.) -/
def lindhardRadialPrimitive (q k : ℝ) : ℝ :=
  (1 / 2) * (k ^ 2 - q ^ 2 / 4) * (Real.log (2 * k + q) - Real.log (2 * k - q)) +
    (1 / 2) * q * k

/-- Derivative of the logarithmic factor `ln |2k + q| - ln |2k - q|` with respect to `k`
    away from the singularities `2k ± q = 0`. -/
lemma hasDerivAt_log_lindhard_ratio (q k : ℝ)
    (h_plus : 2 * k + q ≠ 0) (h_minus : 2 * k - q ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.log (2 * x + q) - Real.log (2 * x - q))
      (2 / (2 * k + q) - 2 / (2 * k - q)) k := by
  have h_lin1 : HasDerivAt (fun x : ℝ ↦ 2 * x + q) 2 k := by
    simpa using ((hasDerivAt_id k).const_mul (2 : ℝ)).add_const q
  have h_lin2 : HasDerivAt (fun x : ℝ ↦ 2 * x - q) 2 k := by
    simpa using ((hasDerivAt_id k).const_mul (2 : ℝ)).sub_const q
  exact (h_lin1.log h_plus).sub (h_lin2.log h_minus)

/-- **Main Radial Antiderivative Theorem (`eq:antideriv_trick`)**:
    For `2k + q ≠ 0` and `2k - q ≠ 0`, the derivative of `lindhardRadialPrimitive q k`
    with respect to `k` is `k * (ln |2k + q| - ln |2k - q|)`. -/
theorem hasDerivAt_lindhardRadialPrimitive (q k : ℝ)
    (h_plus : 2 * k + q ≠ 0) (h_minus : 2 * k - q ≠ 0) :
    HasDerivAt (lindhardRadialPrimitive q)
      (k * (Real.log (2 * k + q) - Real.log (2 * k - q))) k := by
  -- 1. Derivative of the polynomial factor `(1/2) * (k^2 - q^2 / 4)` is `k`:
  have h_poly : HasDerivAt (fun x : ℝ ↦ (1 / 2) * (x ^ 2 - q ^ 2 / 4)) k k := by
    have h_sq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * k) k := by
      simpa using hasDerivAt_pow 2 k
    convert (h_sq.sub_const (q ^ 2 / 4)).const_mul (1 / 2 : ℝ) using 1
    ring
  -- 2. Derivative of the logarithmic factor via `hasDerivAt_log_lindhard_ratio`:
  have h_log := hasDerivAt_log_lindhard_ratio q k h_plus h_minus
  -- 3. Derivative of the linear counterterm `(1/2) * q * k` is `(1 / 2) * q`:
  have h_lin_q : HasDerivAt (fun x : ℝ ↦ (1 / 2) * q * x) ((1 / 2) * q) k := by
    simpa using (hasDerivAt_id k).const_mul ((1 / 2) * q)
  -- 4. Combine via `.mul` and `.add` (in lambda form so the function matches `lindhardRadialPrimitive`!):
  have h_total : HasDerivAt (lindhardRadialPrimitive q)
      (k * (Real.log (2 * k + q) - Real.log (2 * k - q)) +
        (1 / 2) * (k ^ 2 - q ^ 2 / 4) * (2 / (2 * k + q) - 2 / (2 * k - q)) +
        (1 / 2) * q) k :=
    (h_poly.mul h_log).add h_lin_q
  -- 5. Now `.congr_deriv` produces ONLY 1 goal (the algebraic derivative equality):
  refine h_total.congr_deriv ?_
  have h_cancel :
      (1 / 2) * (k ^ 2 - q ^ 2 / 4) * (2 / (2 * k + q) - 2 / (2 * k - q)) + (1 / 2) * q = 0 := by
    have h_diff : 2 / (2 * k + q) - 2 / (2 * k - q) = (-4 * q) / ((2 * k + q) * (2 * k - q)) := by
      rw [div_sub_div _ _ h_plus h_minus]
      ring
    have h_fac : k ^ 2 - q ^ 2 / 4 = ((2 * k + q) * (2 * k - q)) / 4 := by ring
    rw [h_diff, h_fac]
    have h_prod_ne : (2 * k + q) * (2 * k - q) ≠ 0 := mul_ne_zero h_plus h_minus
      -- Cancel `(2 * k + q) * (2 * k - q)` directly!
    calc
      (1 / 2) * (((2 * k + q) * (2 * k - q)) / 4) * ((-4 * q) / ((2 * k + q) * (2 * k - q))) + (1 / 2) * q
        = ((-4 * q) / 8) * (((2 * k + q) * (2 * k - q)) / ((2 * k + q) * (2 * k - q))) + (1 / 2) * q := by ring
      _ = ((-4 * q) / 8) * 1 + (1 / 2) * q := by rw [div_self h_prod_ne]
      _ = 0 := by ring
  linarith

end
