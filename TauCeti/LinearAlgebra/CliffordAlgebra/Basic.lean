/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# Basic Clifford algebra API

This file records general scalar properties of a Clifford algebra obtained from Mathlib's
linear equivalence with the exterior algebra, and the commutation rule
`CliffordAlgebra.ι_mul_ι_eq_ι_smul_sub_mul_ι` moving a vector past another, together with the
square of a scalar plus a vector (`CliffordAlgebra.algebraMap_add_ι_mul_self`) and the
extensionality of algebra equivalences on generators (`CliffordAlgebra.algEquiv_ext_ι`).
A vector squares to its scalar inside a product (`CliffordAlgebra.ι_mul_ι_mul_eq_algebraMap_mul`),
and `(e f) (f e) = Q e Q f` (`CliffordAlgebra.ι_mul_ι_mul_ι_mul_ι_swap`).
Rescaling the factors of a product of vectors pulls the scalars out in front
(`CliffordAlgebra.prod_map_ι_smul`).

For a free module, in every characteristic, `-Q` is the quadratic form of a bilinear form
(Mathlib's `LinearMap.BilinMap.toQuadraticMap_surjective`), so `CliffordAlgebra.changeForm`
compares `C(Q)` with the exterior algebra. This gives linear left inverses of `ι` and of the
scalars (`CliffordAlgebra.exists_leftInverse_ι_of_free`,
`CliffordAlgebra.exists_leftInverse_algebraMap_of_free`), hence injectivity of `ι` and of the
scalars (`CliffordAlgebra.ι_injective_of_free`, `CliffordAlgebra.algebraMap_injective_of_free`),
and invertibility of `Q(m)` for an invertible vector `ι(m)`
(`CliffordAlgebra.isUnit_of_isUnit_ι_of_free`).

Twisted conjugation `ι m ↦ involute x * ι m * x⁻¹` by a unit preserves the square of a vector
(`CliffordAlgebra.algebraMap_apply_eq_of_ι_eq_involute_mul_ι_mul_inv`), in every characteristic.
-/

public section


universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- `CliffordAlgebra.equivExterior` sends a scalar to the corresponding scalar of the exterior
algebra. -/
theorem equivExterior_algebraMap (Q : QuadraticForm R M) [Invertible (2 : R)] (r : R) :
    equivExterior Q (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (ExteriorAlgebra R M) r :=
  changeForm_algebraMap changeForm.associated_neg_proof r

/-- **The scalars of a Clifford algebra are a faithful copy of `R`.** -/
theorem algebraMap_injective (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s hrs
  have h := congrArg (equivExterior Q) hrs
  rwa [equivExterior_algebraMap, equivExterior_algebraMap,
    ExteriorAlgebra.algebraMap_inj M] at h

/-- The scalar action on a Clifford algebra is faithful when `2` is invertible. With this
instance, Mathlib's scalar `iff` lemmas apply directly. -/
instance faithfulSMul (Q : QuadraticForm R M) [Invertible (2 : R)] :
    FaithfulSMul R (CliffordAlgebra Q) :=
  (faithfulSMul_iff_algebraMap_injective R (CliffordAlgebra Q)).2 (algebraMap_injective Q)

/-- **`2` is nonzero in a Clifford algebra** over a nontrivial coefficient ring in which `2` is
invertible, because the scalars are a faithful copy of `R`. As an instance this makes `two_ne_zero`
and the rest of Mathlib's `NeZero (2 : _)` API available inside the Clifford algebra. -/
instance neZeroTwo (Q : QuadraticForm R M) [Nontrivial R] [Invertible (2 : R)] :
    NeZero (2 : CliffordAlgebra Q) :=
  ⟨fun h ↦ Invertible.ne_zero (2 : R) (algebraMap_injective Q
    (((map_ofNat (algebraMap R (CliffordAlgebra Q)) 2).trans h).trans (map_zero _).symm))⟩

/-- Moving a vector `m` past `ι Q v` replaces it by `r • v - m`, where `r * Q v` is the polar
pairing. This description is unchanged when `Q` is replaced by `-Q`. -/
theorem ι_mul_ι_eq_ι_smul_sub_mul_ι {Q : QuadraticForm R M} (v m : M) {r : R}
    (hr : r * Q v = QuadraticMap.polar Q v m) :
    ι Q v * ι Q m = ι Q (r • v - m) * ι Q v := by
  rw [map_sub, map_smul, sub_mul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def,
    ← map_mul (algebraMap R (CliffordAlgebra Q)), hr,
    ← ι_mul_ι_add_swap, add_sub_cancel_right]

/-- The square of an element `r + ι Q t` of the first filtration step: its vector part is
`ι Q ((2 * r) • t)`. -/
theorem algebraMap_add_ι_mul_self (Q : QuadraticForm R M) (r : R) (t : M) :
    (algebraMap R (CliffordAlgebra Q) r + ι Q t) * (algebraMap R _ r + ι Q t) =
      algebraMap R _ (r * r + Q t) + ι Q ((2 * r) • t) := by
  rw [add_mul, mul_add, mul_add, ι_sq_scalar, ← map_mul, ← Algebra.commutes r (ι Q t),
    ← Algebra.smul_def, map_add, map_smul, mul_smul, two_smul]
  abel

/-- A vector squares to its quadratic form value, also inside a product: `x (x y) = Q x y`. -/
theorem ι_mul_ι_mul_eq_algebraMap_mul {Q : QuadraticForm R M} (x : M) (y : CliffordAlgebra Q) :
    ι Q x * (ι Q x * y) = algebraMap R _ (Q x) * y := by
  rw [← mul_assoc, ι_sq_scalar]

/-- The product `(e f) (f e)` of two vectors and their swap is the scalar `Q e * Q f`. -/
theorem ι_mul_ι_mul_ι_mul_ι_swap {Q : QuadraticForm R M} (e f : M) :
    ι Q e * ι Q f * (ι Q f * ι Q e) = algebraMap R _ (Q e * Q f) := by
  rw [mul_assoc, ι_mul_ι_mul_eq_algebraMap_mul, Algebra.commutes, ← mul_assoc, ι_sq_scalar, map_mul]

/-- Two algebra equivalences out of a Clifford algebra agree when they agree on the generators:
the equivalence form of `CliffordAlgebra.hom_ext`. -/
theorem algEquiv_ext_ι {Q : QuadraticForm R M} {A : Type*} [Semiring A] [Algebra R A]
    {φ ψ : CliffordAlgebra Q ≃ₐ[R] A} (h : ∀ v, φ (ι Q v) = ψ (ι Q v)) : φ = ψ :=
  AlgEquiv.coe_toAlgHom_injective <| hom_ext <| LinearMap.ext h

/-- Rescaling every factor of a product of vectors collects the product of the scalars in front
of the product. -/
theorem prod_map_ι_smul (Q : QuadraticForm R M) (c : M → R) (l : List M) :
    ((l.map fun v ↦ c v • v).map (ι Q)).prod = (l.map c).prod • (l.map (ι Q)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_smul, ih, smul_mul_smul_comm]

private theorem two_smul_contractLeft_associated [Invertible (2 : R)]
    (Q : QuadraticForm R M) (v : M) (x : CliffordAlgebra Q) :
    (2 : R) • contractLeft (Q.associated v) x =
      ι Q v * x - involute x * ι Q v := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.commutes]
  | add x y hx hy =>
      rw [map_add, smul_add, hx, hy, map_add, mul_add, add_mul]
      abel
  | ι_mul a x hx =>
      rw [contractLeft_ι_mul, smul_sub, smul_smul, ← mul_smul_comm, hx, map_mul, involute_ι]
      simp only [neg_mul, sub_neg_eq_add]
      have hpolar := LinearMap.congr_fun (LinearMap.congr_fun
        (QuadraticMap.two_nsmul_associated R Q) v) x
      simp only [LinearMap.smul_apply, nsmul_eq_mul, QuadraticMap.polarBilin_apply_apply] at hpolar
      have hpolar' : (2 : R) * Q.associated v x = QuadraticMap.polar (⇑Q) v x := by
        simpa only [Nat.cast_ofNat] using hpolar
      rw [hpolar', Algebra.smul_def, ← ι_mul_ι_add_swap]
      noncomm_ring

section Exterior

variable {I : Type*} [LinearOrder I]

private noncomputable def exteriorCoordProj
    (b : Module.Basis I R M) (i : I) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i))).comp
    (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i))

private theorem exteriorCoordProj_basis_of_not_mem
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    exteriorCoordProj b i (b.ExteriorAlgebra s) = 0 := by
  rw [exteriorCoordProj, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis]
  simp only [hi, ↓reduceIte]

private theorem exteriorCoordProj_basis_of_mem
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    exteriorCoordProj b i (b.ExteriorAlgebra s) = b.ExteriorAlgebra s := by
  rw [exteriorCoordProj, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis]
  simp only [hi, ↓reduceIte]

private theorem exteriorCoordProj_repr_of_mem
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s)
    (x : ExteriorAlgebra R M) :
    b.ExteriorAlgebra.repr (exteriorCoordProj b i x) s =
      b.ExteriorAlgebra.repr x s := by
  have hmap : (b.ExteriorAlgebra.coord s).comp (exteriorCoordProj b i) =
      b.ExteriorAlgebra.coord s := by
    apply b.ExteriorAlgebra.ext
    intro t
    by_cases hit : i ∈ t
    · rw [LinearMap.comp_apply, exteriorCoordProj_basis_of_mem b i t hit]
    · rw [LinearMap.comp_apply, exteriorCoordProj_basis_of_not_mem b i t hit, map_zero]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hts
      · subst t
        exact (hit hi).elim
      · rfl
  exact LinearMap.congr_fun hmap x

private theorem eq_algebraMap_of_all_contractLeft_eq_zero
    (b : Module.Basis I R M) (x : ExteriorAlgebra R M)
    (hx : ∀ d : Module.Dual R M,
      contractLeft (Q := (0 : QuadraticForm R M)) d x = 0) :
    x = algebraMap R (ExteriorAlgebra R M) (b.ExteriorAlgebra.repr x ∅) := by
  have hbempty : b.ExteriorAlgebra (∅ : Finset I) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  apply b.ExteriorAlgebra.repr.injective
  ext s
  rw [Algebra.algebraMap_eq_smul_one, ← hbempty, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_apply]
  by_cases hs : s = ∅
  · subst s
    simp
  · obtain ⟨i, hi⟩ := Finset.ne_empty_iff_nonempty.1 hs
    have hproject : exteriorCoordProj b i x = 0 := by
      rw [exteriorCoordProj, LinearMap.comp_apply, hx, LinearMap.mulLeft_apply, mul_zero]
    have hcoord := exteriorCoordProj_repr_of_mem b i s hi x
    rw [hproject, map_zero, Finsupp.zero_apply] at hcoord
    rw [← hcoord]
    simp [Ne.symm hs]

end Exterior

/-- **Twisted conjugation preserves the square of a vector.** If the twisted conjugate
`involute x * ι m * x⁻¹` of `ι m` by a unit `x` is the vector `ι w`, then `Q w` and `Q m` agree as
scalars of the Clifford algebra, so `Q w = Q m` whenever the scalars embed. -/
theorem algebraMap_apply_eq_of_ι_eq_involute_mul_ι_mul_inv {Q : QuadraticForm R M}
    {x : (CliffordAlgebra Q)ˣ} {w m : M}
    (h : ι Q w = involute (x : CliffordAlgebra Q) * ι Q m * ((x⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) :
    algebraMap R (CliffordAlgebra Q) (Q w) = algebraMap R (CliffordAlgebra Q) (Q m) := by
  -- Applying the grade involution gives the other spelling of the twisted conjugate.
  have h' : ι Q w = (x : CliffordAlgebra Q) * ι Q m *
      involute ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    simpa only [involute_ι, map_mul, involute_involute, mul_neg, neg_mul, neg_inj] using
      congrArg involute h
  calc algebraMap R (CliffordAlgebra Q) (Q w)
      = ι Q w * ι Q w := (ι_sq_scalar Q w).symm
    _ = (involute (x : CliffordAlgebra Q) * ι Q m *
          ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
        ((x : CliffordAlgebra Q) * ι Q m *
          involute ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :=
        congrArg₂ (· * ·) h h'
    _ = involute (x : CliffordAlgebra Q) *
          (ι Q m * (((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * x) * ι Q m) *
        involute ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
        simp only [mul_assoc]
    _ = involute (x : CliffordAlgebra Q) * algebraMap R _ (Q m) *
        involute ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
        rw [Units.inv_mul, mul_one, ι_sq_scalar]
    _ = algebraMap R (CliffordAlgebra Q) (Q m) := by
        -- The scalar `Q m` commutes past `involute x`, which then cancels `involute x⁻¹`.
        rw [← Algebra.commutes, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

/-! ### Free modules in every characteristic -/

section Free

variable [Module.Free R M]

/-- **`ι` has a linear left inverse for a free module**, in every characteristic:
`ExteriorAlgebra.ιInv` after `CliffordAlgebra.changeForm` to the exterior algebra. It is the
counterpart of `CliffordAlgebra.ιInv`, which needs `2` to be invertible. -/
theorem exists_leftInverse_ι_of_free (Q : QuadraticForm R M) :
    ∃ f : CliffordAlgebra Q →ₗ[R] M, Function.LeftInverse f (ι Q) := by
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (0 - Q)
  refine ⟨ExteriorAlgebra.ιInv ∘ₗ changeForm hB, fun m => ?_⟩
  rw [LinearMap.comp_apply, changeForm_ι]
  exact ExteriorAlgebra.ι_leftInverse m

/-- **`ι` is injective for a free module**, in every characteristic. -/
theorem ι_injective_of_free (Q : QuadraticForm R M) : Function.Injective (ι Q) :=
  (exists_leftInverse_ι_of_free Q).choose_spec.injective

/-- **The scalars have a linear left inverse for a free module**, in every characteristic:
`ExteriorAlgebra.algebraMapInv` after `CliffordAlgebra.changeForm` to the exterior algebra. -/
theorem exists_leftInverse_algebraMap_of_free (Q : QuadraticForm R M) :
    ∃ f : CliffordAlgebra Q →ₗ[R] R,
      Function.LeftInverse f (algebraMap R (CliffordAlgebra Q)) := by
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (0 - Q)
  refine ⟨(ExteriorAlgebra.algebraMapInv (R := R) (M := M)).toLinearMap ∘ₗ changeForm hB,
    fun r => ?_⟩
  rw [LinearMap.comp_apply, changeForm_algebraMap, AlgHom.toLinearMap_apply]
  exact ExteriorAlgebra.algebraMap_leftInverse M r

/-- **The scalars embed in the Clifford algebra of a free module**, in every characteristic. -/
theorem algebraMap_injective_of_free (Q : QuadraticForm R M) :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) :=
  (exists_leftInverse_algebraMap_of_free Q).choose_spec.injective

/-- **An invertible vector has invertible square** for a free module, in every characteristic:
if `ι(m)` is a unit then so is `Q(m)`. -/
theorem isUnit_of_isUnit_ι_of_free {Q : QuadraticForm R M} {m : M} (h : IsUnit (ι Q m)) :
    IsUnit (Q m) := by
  have hsq : IsUnit (algebraMap R (CliffordAlgebra Q) (Q m)) := by
    rw [← ι_sq_scalar]
    exact h.mul h
  obtain ⟨f, hf⟩ := exists_leftInverse_algebraMap_of_free Q
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    hsq.algebraMap_of_algebraMap f (by simpa only [map_one] using hf 1)

end Free

/-- A Clifford element annihilated by every left contraction is a scalar. -/
theorem exists_eq_algebraMap_of_contractLeft_eq_zero [Module.Free R M]
    (Q : QuadraticForm R M) (x : CliffordAlgebra Q)
    (hx : ∀ d : Module.Dual R M, contractLeft d x = 0) :
    ∃ r : R, x = algebraMap R (CliffordAlgebra Q) r := by
  -- the exterior basis needs a linear order on the index type; any classical one will do
  classical
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  obtain ⟨B, h⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (0 - Q)
  let y : ExteriorAlgebra R M := changeForm h x
  have hycontract (d : Module.Dual R M) :
      contractLeft (Q := (0 : QuadraticForm R M)) d y = 0 := by
    dsimp only [y]
    rw [← changeForm_contractLeft h d x, hx, map_zero]
  let r := b.ExteriorAlgebra.repr y ∅
  refine ⟨r, ?_⟩
  apply (changeFormEquiv h).injective
  simpa only [y, r, changeFormEquiv_apply, changeForm_algebraMap] using
    eq_algebraMap_of_all_contractLeft_eq_zero b y hycontract

variable {K : Type u} [Field K] [Module K M] [FiniteDimensional K M]
  [Invertible (2 : K)]

/-- A Clifford element that graded-commutes with every generating vector is a scalar. Here
`involute x * ι v = ι v * x` is the uniform equation combining commutation of the even part
with anticommutation of the odd part. -/
theorem exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul
    (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q)
    (hx : ∀ v : M, involute x * ι Q v = ι Q v * x) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hB : B.Nondegenerate := by
    simpa only [B] using QuadraticMap.nondegenerate_associated_iff.mpr hQ
  apply exists_eq_algebraMap_of_contractLeft_eq_zero Q x
  intro d
  obtain ⟨v, rfl⟩ := (B.toDual hB).surjective d
  have htoDual : B.toDual hB v = Q.associated v :=
    LinearMap.ext fun w ↦ (LinearMap.BilinForm.toDual_def hB).trans (by rfl)
  rw [htoDual]
  apply (isUnit_of_invertible (2 : K)).smul_eq_zero.mp
  rw [two_smul_contractLeft_associated Q, hx v, sub_self]

/-- An even Clifford element that commutes with every generating vector is a scalar. -/
theorem exists_eq_algebraMap_of_mem_even_of_commute
    (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q)
    (hx_even : x ∈ even Q) (hx_comm : ∀ v : M, Commute x (ι Q v)) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  apply exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul Q hQ x
  intro v
  rw [involute_eq_of_mem_even hx_even, (hx_comm v).eq]

end CliffordAlgebra
