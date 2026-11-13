/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Split.Class
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.NumberTheory.IntegralLattice.Binary.Genus
import TauCeti.Data.ZMod.SquareMultiple
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The genus of a binary lattice of square discriminant

Let `L` be a binary lattice of content `c` whose primitive norm form has nonzero square
discriminant `s²`. Its oriented proper class lies in the group of split proper classes, which is
`(ℤ/sℤ)ˣ` through the triangular representatives `sxy + ay²`. This file proves that the genus of
`L` is a coset of the subgroup of squares: two such lattices lie in one genus exactly when they
have the same content and their classes differ by a square
(`IntegralLattice.sameGenus_iff_binaryContent_eq_and_isSquare_inv_mul_binarySplitProperClass`).

Both directions are local computations in a triangular basis, whose Gram matrix is
`!![0, cs/2; cs/2, ca]`.

* If `a' ≡ a z² (mod s)`, lift `z` to an integer `u` coprime to `s`. Over `ℤ_p` with `p ∣ s`, the
  basis `u⁻¹ e₀, t e₀ + u e₁` with `t = (a' - a u²) / (s u)` carries one Gram matrix to the other,
  and at the remaining primes and over `ℚ` a unipotent change `e₁ ↦ e₁ + t e₀` does the same. The
  rational isometry supplies the equality of signatures.
* Conversely, an isometry of the localizations at `p` sends the second basis vector of `M_p` to
  a vector `x e₀ + y e₁` of `L_p` of the same norm, so `ca' = c(sxy + ay²)` in `ℤ_p`. Hence
  `a' ≡ a y² (mod p ^ k)` for every prime power `p ^ k` dividing `s`, and these congruences glue
  by the Chinese remainder theorem (`ZMod.exists_intCast_eq_mul_sq_iff`).

The general step, isometry of two binary forms with an isotropic first basis vector, is
`LinearMap.BilinForm.equivalent_of_toMatrix_eq_isotropic`.

## Main results

* `LinearMap.BilinForm.equivalent_of_toMatrix_eq_isotropic`: forms with Gram matrices
  `!![0, β; β, γ]` and `!![0, β; β, 2tμβ + μ²γ]`, for a unit `μ`, are isometric.
* `IntegralLattice.exists_binaryNormForm_eq_smul_splitTriangularForm`: a lattice whose
  split class is that of `sxy + ay²` has a basis with norm form `c (sxy + ay²)`.
* `IntegralLattice.sameGenus_iff_binaryContent_eq_and_isSquare_inv_mul_binarySplitProperClass`:
  lattices of primitive discriminant `s²` lie in one genus exactly when their contents agree and
  their split classes differ by a square.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §3 (genus theory of binary forms).
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, for integral local equivalence.
-/

public section

open Module

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

/-- **Binary forms with an isotropic first basis vector.** Suppose that `B` and `B'` have Gram
matrices `!![0, β; β, γ]` and `!![0, β; β, γ']` in bases `v` and `w`. If `γ' = 2tμβ + μ²γ` for a
unit `μ`, then `B` and `B'` are isometric: in the basis `μ⁻¹ v₀, t v₀ + μ v₁` the form `B` has the
Gram matrix of `B'`. -/
theorem equivalent_of_toMatrix_eq_isotropic {B : BilinForm R M} {B' : BilinForm R M'}
    (v : Basis (Fin 2) R M) (w : Basis (Fin 2) R M') {β γ γ' t : R} (μ : Rˣ)
    (hB : toMatrix v B = !![0, β; β, γ]) (hB' : toMatrix w B' = !![0, β; β, γ'])
    (h : γ' = 2 * t * μ * β + μ ^ 2 * γ) : B.Equivalent B' := by
  let P : Matrix (Fin 2) (Fin 2) R := !![((μ⁻¹ : Rˣ) : R), t; 0, μ]
  have hP : IsUnit P.det := by simp [P, Matrix.det_fin_two_of]
  let E := v.map (Matrix.toLinearEquiv v P hP)
  have hE0 : E 0 = ((μ⁻¹ : Rˣ) : R) • v 0 := by
    simp [E, P, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_two]
  have hE1 : E 1 = t • v 0 + (μ : R) • v 1 := by
    simp [E, P, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_two]
  have hv (i j : Fin 2) : B (v i) (v j) = !![0, β; β, γ] i j := by
    rw [← hB, toMatrix_apply]
  refine ⟨E.isometryEquivOfToMatrixEq w ?_⟩
  rw [hB', h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix_apply, hE0, hE1, hv]
  ring

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

open BinaryQuadraticForm

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **Triangular bases.** If the oriented split class of a binary lattice is the class of the
triangular form `sxy + ay²`, then some carrier basis has norm form `c (sxy + ay²)`, where `c` is the
content. -/
theorem exists_binaryNormForm_eq_smul_splitTriangularForm (L : IntegralLattice V)
    (hV : finrank ℚ V = 2) (s : ℕ) [NeZero s] (hD : L.binaryDiscriminant hV = (s : ℤ) ^ 2)
    (o : Orientation ℤ L (Fin 2)) {a : ℤ} (ha : IsCoprime (s : ℤ) a)
    (h : L.binarySplitProperClass hV s hD o = splitProperClassMk s a ha) :
    ∃ b : Basis (Fin 2) ℤ L,
      L.binaryNormForm b = (L.binaryContent hV : ℤ) • splitTriangularForm s a := by
  let b₀ := (Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)).adjustToOrientation o
  have hcls := congrArg (splitProperClassToProperClass s) h
  rw [binarySplitProperClass_toProperClass, splitProperClassToProperClass_splitProperClassMk,
    L.binaryProperClass_eq_mk b₀ hV o (Basis.orientation_adjustToOrientation _ _)] at hcls
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hcls))
  obtain ⟨b, hb⟩ := L.exists_binaryNormForm_eq_smul b₀ γ⁻¹
  refine ⟨b, ?_⟩
  rw [hb, ← (L.binaryNormForm b₀).content_smul_primPart, ← hγ, smul_comm, inv_smul_smul,
    L.binaryContent_eq_content_binaryNormForm b₀ hV, Nat.cast_smul_eq_nsmul]

section Triangular

variable {L : IntegralLattice V} {M : IntegralLattice W} {b : Basis (Fin 2) ℤ L}
  {b' : Basis (Fin 2) ℤ M} {c s a a' : ℤ}

/-- In a basis with norm form `c (sxy + ay²)`, the Gram matrix is `!![0, β; β, ca]` with
`2β = cs`. -/
private theorem gramMatrix_eq_of_binaryNormForm_eq
    (hb : L.binaryNormForm b = c • splitTriangularForm s a) :
    L.gramMatrix b 0 0 = 0 ∧ 2 * L.gramMatrix b 0 1 = c * s ∧
      L.gramMatrix b 1 0 = L.gramMatrix b 0 1 ∧ L.gramMatrix b 1 1 = c * a := by
  have ha := congrArg BinaryQuadraticForm.a hb
  have hb' := congrArg BinaryQuadraticForm.b hb
  have hc := congrArg BinaryQuadraticForm.c hb
  simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, smul_a', smul_b', smul_c',
    splitTriangularForm_def, smul_eq_mul, mul_zero] at ha hb' hc
  exact ⟨ha, hb', (L.isSymm_gramMatrix b).apply 0 1, hc⟩

/-- Two lattices with triangular norm forms `c (sxy + ay²)` and `c (sxy + a'y²)` become isometric
over any commutative ring `R` in which `a' = stμ + μ²a` for a unit `μ`. The forms over `R` are
given through bases in which their matrices are the integral Gram matrices. -/
private theorem equivalent_of_toMatrix_eq_map_gramMatrix {R N N' : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    {B : LinearMap.BilinForm R N} {B' : LinearMap.BilinForm R N'}
    (hb : L.binaryNormForm b = c • splitTriangularForm s a)
    (hb' : M.binaryNormForm b' = c • splitTriangularForm s a')
    (v : Basis (Fin 2) R N) (w : Basis (Fin 2) R N')
    (hv : LinearMap.BilinForm.toMatrix v B = (L.gramMatrix b).map (Int.cast : ℤ → R))
    (hw : LinearMap.BilinForm.toMatrix w B' = (M.gramMatrix b').map (Int.cast : ℤ → R))
    (μ : Rˣ) (t : R) (h : (a' : R) = s * t * μ + μ ^ 2 * a) : B.Equivalent B' := by
  obtain ⟨h00, h01, h10, h11⟩ := gramMatrix_eq_of_binaryNormForm_eq hb
  obtain ⟨h00', h01', h10', h11'⟩ := gramMatrix_eq_of_binaryNormForm_eq hb'
  have hβ : M.gramMatrix b' 0 1 = L.gramMatrix b 0 1 := by omega
  have hβR : 2 * (L.gramMatrix b 0 1 : R) = c * s := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using congrArg (Int.cast : ℤ → R) h01
  refine LinearMap.BilinForm.equivalent_of_toMatrix_eq_isotropic v w μ
    (β := (L.gramMatrix b 0 1 : R)) (γ := c * a) (γ' := c * a') (t := t) ?_ ?_ ?_
  · rw [hv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [-gramMatrix_apply, h00, h10, h11]
  · rw [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [-gramMatrix_apply, h00', h10', h11', hβ]
  · linear_combination (c : R) * h - t * μ * hβR

/-- **Triangular lattices whose coefficients differ by a square modulo `s` share a genus.** If
`L` and `M` have norm forms `c (sxy + ay²)` and `c (sxy + a'y²)` and `a' ≡ a z² (mod s)`, then `L`
and `M` lie in one genus. -/
private theorem sameGenus_of_intCast_eq_mul_sq {s : ℕ} [NeZero s]
    (hb : L.binaryNormForm b = c • splitTriangularForm s a)
    (hb' : M.binaryNormForm b' = c • splitTriangularForm s a') (ha' : IsCoprime (s : ℤ) a')
    {z : ZMod s} (hz : (a' : ZMod s) = a * z ^ 2) : L.SameGenus M := by
  -- The residue `z` is a unit, since `a'` is; lift it to an integer `u` coprime to `s`.
  have ha'u : IsUnit (a' : ZMod s) := (ZMod.unitOfIsCoprime a' ha'.symm).isUnit
  have hzu : IsUnit z := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_right (hz ▸ ha'u))
  set u : ℤ := (z.val : ℤ)
  have hu : IsCoprime (s : ℤ) u :=
    (Nat.isCoprime_iff_coprime.mpr ((ZMod.isUnit_iff_coprime z.val s).mp
      (by rwa [ZMod.natCast_zmod_val]))).symm
  obtain ⟨r, hr⟩ : (s : ℤ) ∣ a' - a * u ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [u, ZMod.natCast_zmod_val]
    rw [hz, sub_self]
  -- Over `ℚ` the forms are isometric through `μ = 1` and `t = (a' - a) / s`.
  have hform : L.form.Equivalent M.form := by
    refine equivalent_of_toMatrix_eq_map_gramMatrix hb hb' (b.extendOfIsLattice ℚ)
      (b'.extendOfIsLattice ℚ) ?_ ?_ 1 ((a' - a) / s) ?_
    · rw [← map_gramMatrix, algebraMap_int_eq, Int.coe_castRingHom]
    · rw [← map_gramMatrix, algebraMap_int_eq, Int.coe_castRingHom]
    · have hsQ : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
      push_cast
      field_simp
      ring
  refine (sameGenus_iff_localIntegralForm_equivalent hform).mpr fun p _ ↦ ?_
  by_cases hp : (p : ℤ) ∣ s
  · -- At a prime dividing `s`, take `μ = u`, a unit since `u` is coprime to `s`.
    have hup : IsUnit (u : ℤ_[p]) := PadicInt.isUnit_intCast_iff.mpr fun hpu ↦
      (Fact.out : p.Prime).ne_one
        (by simpa using Int.isUnit_iff_natAbs_eq.mp (hu.isUnit_of_dvd' hp hpu))
    exact equivalent_of_toMatrix_eq_map_gramMatrix hb hb' _ _ (toMatrix_localIntegralForm L p b)
      (toMatrix_localIntegralForm M p b') hup.unit (r * ↑hup.unit⁻¹) (by
        rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one, IsUnit.unit_spec]
        exact_mod_cast (by linear_combination hr : a' = s * r + u ^ 2 * a))
  · -- At a prime not dividing `s`, the coefficient `s` is a unit; take `μ = 1`.
    have hsp : IsUnit ((s : ℤ) : ℤ_[p]) := PadicInt.isUnit_intCast_iff.mpr hp
    exact equivalent_of_toMatrix_eq_map_gramMatrix hb hb' _ _ (toMatrix_localIntegralForm L p b)
      (toMatrix_localIntegralForm M p b') 1 ((a' - a) * ↑hsp.unit⁻¹) (by
        rw [Units.val_one, mul_one, one_pow, one_mul, mul_left_comm, hsp.mul_val_inv, mul_one,
          sub_add_cancel])

/-- **A local isometry forces a square congruence.** If `L` and `M` have norm forms
`c (sxy + ay²)` and `c (sxy + a'y²)` with `c ≠ 0` and their localizations at `p` are isometric,
then `a' ≡ a z² (mod p ^ k)` for every prime power `p ^ k` dividing `s`. -/
private theorem exists_intCast_eq_mul_sq_of_localIntegralForm_equivalent (hc : c ≠ 0)
    (hb : L.binaryNormForm b = c • splitTriangularForm s a)
    (hb' : M.binaryNormForm b' = c • splitTriangularForm s a') {p k : ℕ} [Fact p.Prime]
    (hk : ((p ^ k : ℕ) : ℤ) ∣ s) (h : (L.localIntegralForm p).Equivalent (M.localIntegralForm p)) :
    ∃ z : ZMod (p ^ k), (a' : ZMod (p ^ k)) = a * z ^ 2 := by
  obtain ⟨φ⟩ := h
  obtain ⟨h00, h01, h10, h11⟩ := gramMatrix_eq_of_binaryNormForm_eq hb
  obtain ⟨-, -, -, h11'⟩ := gramMatrix_eq_of_binaryNormForm_eq hb'
  let e := b.baseChange ℤ_[p]
  have hL (i j : Fin 2) : L.localIntegralForm p (e i) (e j) = (L.gramMatrix b i j : ℤ_[p]) := by
    rw [← LinearMap.BilinForm.toMatrix_apply, toMatrix_localIntegralForm, Matrix.map_apply]
  have hM : M.localIntegralForm p (b'.baseChange ℤ_[p] 1) (b'.baseChange ℤ_[p] 1) =
      (M.gramMatrix b' 1 1 : ℤ_[p]) := by
    rw [← LinearMap.BilinForm.toMatrix_apply, toMatrix_localIntegralForm, Matrix.map_apply]
  -- Write the preimage of the second basis vector of `M_p` as `x e₀ + y e₁` in `L_p`.
  set v := φ.symm (b'.baseChange ℤ_[p] 1)
  set x := e.repr v 0
  set y := e.repr v 1
  have hv : v = x • e 0 + y • e 1 := by
    simpa only [Fin.sum_univ_two] using (e.sum_repr v).symm
  have hval : M.localIntegralForm p (b'.baseChange ℤ_[p] 1) (b'.baseChange ℤ_[p] 1) =
      L.localIntegralForm p v v := by
    rw [← φ.map_app v v, LinearMap.BilinForm.IsometryEquiv.apply_symm_apply]
  rw [hM, h11', hv] at hval
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hL, h00,
    h10, h11] at hval
  have hβ : 2 * (L.gramMatrix b 0 1 : ℤ_[p]) = c * s := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using congrArg (Int.cast : ℤ → ℤ_[p]) h01
  -- Cancelling `c` gives `a' = sxy + ay²` in `ℤ_p`; reduce modulo `p ^ k`.
  have key : (a' : ℤ_[p]) = s * x * y + a * y ^ 2 := by
    refine mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : ℤ_[p]) ≠ 0) ?_
    push_cast at hval
    linear_combination hval + x * y * hβ
  refine ⟨PadicInt.toZModPow k y, ?_⟩
  have hs : (s : ZMod (p ^ k)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd s (p ^ k)).mpr hk
  simpa only [map_intCast, map_add, map_mul, map_pow, hs, zero_mul, zero_add] using
    congrArg (PadicInt.toZModPow k) key

end Triangular

/-- **The genus of a binary lattice of square discriminant is a coset of the squares.** Let `L` and
`M` be binary lattices of primitive discriminant `s²`, `s ≠ 0`, with chosen orientations. They lie
in one genus exactly when they have the same content and their split proper classes differ by a
square in the group `(ℤ/sℤ)ˣ` of split proper classes. In particular the right-hand side does not
depend on the chosen orientations. -/
theorem sameGenus_iff_binaryContent_eq_and_isSquare_inv_mul_binarySplitProperClass
    {L : IntegralLattice V} {M : IntegralLattice W} (hV : finrank ℚ V = 2)
    (hW : finrank ℚ W = 2) (s : ℕ) [NeZero s]
    (hL : L.binaryDiscriminant hV = (s : ℤ) ^ 2) (hM : M.binaryDiscriminant hW = (s : ℤ) ^ 2)
    (oL : Orientation ℤ L (Fin 2)) (oM : Orientation ℤ M (Fin 2)) :
    L.SameGenus M ↔ L.binaryContent hV = M.binaryContent hW ∧
      IsSquare ((L.binarySplitProperClass hV s hL oL)⁻¹ * M.binarySplitProperClass hW s hM oM) := by
  obtain ⟨a, ha, hqL⟩ := exists_eq_splitProperClassMk s (L.binarySplitProperClass hV s hL oL)
  obtain ⟨a', ha', hqM⟩ := exists_eq_splitProperClassMk s (M.binarySplitProperClass hW s hM oM)
  obtain ⟨b, hb⟩ := L.exists_binaryNormForm_eq_smul_splitTriangularForm hV s hL oL ha hqL
  obtain ⟨b', hb'⟩ := M.exists_binaryNormForm_eq_smul_splitTriangularForm hW s hM oM ha' hqM
  rw [hqL, hqM, isSquare_inv_mul_splitProperClassMk_iff]
  constructor
  · intro h
    have hc := h.binaryContent_eq hV hW
    refine ⟨hc, (ZMod.exists_intCast_eq_mul_sq_iff (NeZero.ne s) a' a).mpr fun p k hp hk ↦ ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have hc0 : (L.binaryContent hV : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (L.binaryContent_pos hV
      (L.form_ne_zero_of_binaryDiscriminant_ne_zero hV (by simp [hL, NeZero.ne s]))).ne'
    rw [← hc] at hb'
    exact exists_intCast_eq_mul_sq_of_localIntegralForm_equivalent hc0 hb hb'
      (Int.natCast_dvd_natCast.mpr hk) (h.localIntegralForm_equivalent p)
  · rintro ⟨hc, z, hz⟩
    rw [← hc] at hb'
    exact sameGenus_of_intCast_eq_mul_sq hb hb' ha' hz

end TauCeti.IntegralLattice
