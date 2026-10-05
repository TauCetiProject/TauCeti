/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Splitting
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization

/-!
# Isometric orthogonal splitting of integral lattices

Orthogonally complementary submodules of an integral carrier give a decomposition of the
entire lattice, including its rational ambient form. Each summand is realized by rationalizing
the restricted integral form with `IntegralLattice.ofIntegralForm`; it need not span the
original ambient space. The resulting isometry sends unit pure tensors to the sum of their
underlying vectors, so the decomposition identifies the actual integral carriers.

A submodule whose restricted pairing is bijective is complementary to its orthogonal
complement. Combining this with the isometry construction gives the unimodular splitting
theorem without assuming nondegeneracy of the whole lattice.

The mathematical source is O. T. O'Meara, *Introduction to Quadratic Forms*, §82.
-/

public section

open TensorProduct

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (S T : Submodule ℤ L)

-- The construction uses `Submodule.prodEquivOfIsCompl`, the carrier equivalence of
-- `IntegralLattice.ofIntegralForm`, and `IntegralLattice.Isometry.ofCarrierEquiv`.
/-- Orthogonally complementary integral submodules give an isometry from the orthogonal sum
of their rationalized restricted forms onto the original lattice. -/
noncomputable def orthogonalSumIsometryOfIsCompl (h : IsCompl S T)
    (horth : T ≤ L.integralForm.orthogonal S) :
    Isometry
      ((ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)).orthogonalSum
        (ofIntegralForm (L.integralForm.restrict T) (L.isSymm_integralForm.restrict T))) L := by
  let LS := ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)
  let LT := ofIntegralForm (L.integralForm.restrict T) (L.isSymm_integralForm.restrict T)
  let eS := ofIntegralForm.carrierEquiv (L.integralForm.restrict S)
    (L.isSymm_integralForm.restrict S)
  let eT := ofIntegralForm.carrierEquiv (L.integralForm.restrict T)
    (L.isSymm_integralForm.restrict T)
  let e := (orthogonalSumCarrierEquiv LS LT).trans
    ((eS.symm.prodCongr eT.symm).trans (S.prodEquivOfIsCompl T h))
  refine Isometry.ofCarrierEquiv e ?_
  intro x y
  have hST (s : S) (t : T) : L.integralForm s t = 0 := horth t.2 s s.2
  have hTS (t : T) (s : S) : L.integralForm t s = 0 := by
    rw [L.isSymm_integralForm.eq]
    exact hST s t
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl',
    map_add, LinearMap.add_apply, hST, hTS, add_zero, zero_add]
  rw [integralForm_orthogonalSum]
  simp only [orthogonalSumFst_apply, orthogonalSumSnd_apply]
  have hs (a b : LS) : L.integralForm (eS.symm a) (eS.symm b) = LS.integralForm a b := by
    simpa only [LS, eS, LinearEquiv.apply_symm_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply] using
      (ofIntegralForm.integralForm_carrierEquiv (L.integralForm.restrict S)
        (L.isSymm_integralForm.restrict S) (eS.symm a) (eS.symm b)).symm
  have ht (a b : LT) : L.integralForm (eT.symm a) (eT.symm b) = LT.integralForm a b := by
    simpa only [LT, eT, LinearEquiv.apply_symm_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply] using
      (ofIntegralForm.integralForm_carrierEquiv (L.integralForm.restrict T)
        (L.isSymm_integralForm.restrict T) (eT.symm a) (eT.symm b)).symm
  exact congrArg₂ (· + ·) (hs _ _) (ht _ _)

/-- On unit pure tensors the splitting isometry is addition of the original integral vectors. -/
theorem orthogonalSumIsometryOfIsCompl_apply_one_tmul (h : IsCompl S T)
    (horth : T ≤ L.integralForm.orthogonal S) (s : S) (t : T) :
    L.orthogonalSumIsometryOfIsCompl S T h horth (1 ⊗ₜ[ℤ] s, 1 ⊗ₜ[ℤ] t) =
      ((s : L) : V) + ((t : L) : V) := by
  let es := ofIntegralForm.carrierEquiv (L.integralForm.restrict S)
    (L.isSymm_integralForm.restrict S)
  let et := ofIntegralForm.carrierEquiv (L.integralForm.restrict T)
    (L.isSymm_integralForm.restrict T)
  let x := (orthogonalSumCarrierEquiv _ _).symm (es s, et t)
  have hx : (x : (ℚ ⊗[ℤ] S) × (ℚ ⊗[ℤ] T)) = (1 ⊗ₜ[ℤ] s, 1 ⊗ₜ[ℤ] t) := by
    apply Prod.ext
    · rw [← coe_orthogonalSumCarrierEquiv_fst]
      simp [x, es]
    · rw [← coe_orthogonalSumCarrierEquiv_snd]
      simp [x, et]
  rw [← hx, ← Isometry.coe_carrierEquiv_apply]
  simp [orthogonalSumIsometryOfIsCompl, Isometry.carrierEquiv_ofCarrierEquiv,
    x, es, et]

/-- On arbitrary pure tensors the splitting isometry is the sum of the scalar multiples of
the original vectors. -/
@[simp]
theorem orthogonalSumIsometryOfIsCompl_apply_tmul (h : IsCompl S T)
    (horth : T ≤ L.integralForm.orthogonal S) (q r : ℚ) (s : S) (t : T) :
    L.orthogonalSumIsometryOfIsCompl S T h horth (q ⊗ₜ[ℤ] s, r ⊗ₜ[ℤ] t) =
      q • ((s : L) : V) + r • ((t : L) : V) := by
  have hp : (q ⊗ₜ[ℤ] s, r ⊗ₜ[ℤ] t) =
      q • (1 ⊗ₜ[ℤ] s, (0 : ℚ ⊗[ℤ] T)) + r • ((0 : ℚ ⊗[ℤ] S), 1 ⊗ₜ[ℤ] t) := by
    apply Prod.ext <;>
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add] <;>
      exact TensorProduct.tmul_eq_smul_one_tmul _ _
  rw [hp, map_add, map_smul, map_smul]
  have hs := L.orthogonalSumIsometryOfIsCompl_apply_one_tmul S T h horth s 0
  have ht := L.orthogonalSumIsometryOfIsCompl_apply_one_tmul S T h horth 0 t
  simp only [tmul_zero, Submodule.coe_zero, add_zero, zero_add] at hs ht
  rw [hs, ht]

/-- The inverse splitting isometry recovers the two unit pure tensors from a sum of integral
vectors in the two summands. -/
@[simp]
theorem orthogonalSumIsometryOfIsCompl_symm_apply_add (h : IsCompl S T)
    (horth : T ≤ L.integralForm.orthogonal S) (s : S) (t : T) :
    (L.orthogonalSumIsometryOfIsCompl S T h horth).symm
        (((s : L) : V) + ((t : L) : V)) = (1 ⊗ₜ[ℤ] s, 1 ⊗ₜ[ℤ] t) := by
  apply (L.orthogonalSumIsometryOfIsCompl S T h horth).injective
  simp

/-- The inverse splitting isometry recovers arbitrary pure tensors from the corresponding
rational scalar multiples of vectors in the two summands. -/
@[simp]
theorem orthogonalSumIsometryOfIsCompl_symm_apply_smul_add_smul (h : IsCompl S T)
    (horth : T ≤ L.integralForm.orthogonal S) (q r : ℚ) (s : S) (t : T) :
    (L.orthogonalSumIsometryOfIsCompl S T h horth).symm
        (q • ((s : L) : V) + r • ((t : L) : V)) = (q ⊗ₜ[ℤ] s, r ⊗ₜ[ℤ] t) := by
  apply (L.orthogonalSumIsometryOfIsCompl S T h horth).injective
  simp

/-- A submodule with perfect restricted integral pairing splits off isometrically, with its
orthogonal complement rationalized in its own ambient space. -/
noncomputable def orthogonalSplittingIsometry (S : Submodule ℤ L)
    (h : Function.Bijective (L.integralForm.restrict S)) :
    Isometry
      ((ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)).orthogonalSum
        (ofIntegralForm (L.integralForm.restrict (L.integralForm.orthogonal S))
          (L.isSymm_integralForm.restrict (L.integralForm.orthogonal S)))) L :=
  L.orthogonalSumIsometryOfIsCompl S (L.integralForm.orthogonal S)
    (L.isCompl_orthogonal_of_restrict_bijective S h) le_rfl

/-- The unimodular splitting isometry sends unit pure tensors to the sum of their vectors. -/
theorem orthogonalSplittingIsometry_apply_one_tmul (S : Submodule ℤ L)
    (h : Function.Bijective (L.integralForm.restrict S))
    (s : S) (t : L.integralForm.orthogonal S) :
    L.orthogonalSplittingIsometry S h (1 ⊗ₜ[ℤ] s, 1 ⊗ₜ[ℤ] t) =
      ((s : L) : V) + ((t : L) : V) :=
  L.orthogonalSumIsometryOfIsCompl_apply_one_tmul S _ _ _ s t

/-- The unimodular splitting isometry sends arbitrary pure tensors to the sum of the
corresponding rational scalar multiples of their vectors. -/
@[simp]
theorem orthogonalSplittingIsometry_apply_tmul (S : Submodule ℤ L)
    (h : Function.Bijective (L.integralForm.restrict S)) (q r : ℚ)
    (s : S) (t : L.integralForm.orthogonal S) :
    L.orthogonalSplittingIsometry S h (q ⊗ₜ[ℤ] s, r ⊗ₜ[ℤ] t) =
      q • ((s : L) : V) + r • ((t : L) : V) :=
  L.orthogonalSumIsometryOfIsCompl_apply_tmul S _ _ _ q r s t

/-- The inverse unimodular splitting sends a sum of integral vectors in the summand and its
orthogonal complement to their unit pure tensors. -/
@[simp]
theorem orthogonalSplittingIsometry_symm_apply_add (S : Submodule ℤ L)
    (h : Function.Bijective (L.integralForm.restrict S))
    (s : S) (t : L.integralForm.orthogonal S) :
    (L.orthogonalSplittingIsometry S h).symm
        (((s : L) : V) + ((t : L) : V)) = (1 ⊗ₜ[ℤ] s, 1 ⊗ₜ[ℤ] t) :=
  L.orthogonalSumIsometryOfIsCompl_symm_apply_add S _ _ _ s t

/-- The inverse unimodular splitting recovers arbitrary pure tensors from rational scalar
multiples of vectors in the summand and its orthogonal complement. -/
@[simp]
theorem orthogonalSplittingIsometry_symm_apply_smul_add_smul (S : Submodule ℤ L)
    (h : Function.Bijective (L.integralForm.restrict S)) (q r : ℚ)
    (s : S) (t : L.integralForm.orthogonal S) :
    (L.orthogonalSplittingIsometry S h).symm
        (q • ((s : L) : V) + r • ((t : L) : V)) = (q ⊗ₜ[ℤ] s, r ⊗ₜ[ℤ] t) :=
  L.orthogonalSumIsometryOfIsCompl_symm_apply_smul_add_smul S _ _ _ q r s t

end TauCeti.IntegralLattice
