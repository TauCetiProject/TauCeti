/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.TensorProduct
public import TauCeti.Geometry.Hodge.Tate.Basic
public import TauCeti.Geometry.Hodge.Tate.Twist

/-!
# The Tate twist as a tensor product

The Tate twist `V(m)` of a pure Hodge structure `V` of weight `n` is classically defined as the
tensor product `V ⊗ ℤ(m)` with the rank-one Tate structure. The construction
`TauCeti.Hodge.HodgeStructureOn.tateTwist` instead keeps the underlying complex vector space `W`
and shifts the filtration, `F^p(V(m)) = F^{p+m}(V)`. This file compares the two on the complex
side: Mathlib's right unitor `TensorProduct.rid ℂ W : W ⊗[ℂ] ℂ ≃ₗ[ℂ] W` intertwines the
conjugations, and the complex Hodge components and the Hodge filtration of `V(m)` are the pullbacks
of those of `V ⊗ ℤ(m)` along its inverse.

Consequently the weight and filtration shift of `tateTwist` are those of `V ⊗ ℤ(m)`, the Hodge
numbers of `V ⊗ ℤ(m)` are those of `V` translated by `m`, and the Hodge filtration of `ℤ(k + m)`
is that of `ℤ(k) ⊗ ℤ(m)` along the right unitor `ℂ ⊗[ℂ] ℂ ≃ₗ[ℂ] ℂ`.

The convention follows Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1, and
Peters–Steenbrink, *Mixed Hodge Structures*, §2.1. The comparison of components adapts the
decomposition argument of `TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap`.

## Main declarations

* `TauCeti.Hodge.Conjugation.rid_symm_map_conj`: the right unitor intertwines a conjugation with
  its tensor product with the conjugation of the Tate complexification.
* `TauCeti.Hodge.HodgeStructureOn.tateTwist_piece_eq_comap` and
  `TauCeti.Hodge.HodgeStructureOn.tateTwist_F_eq_comap`: the components and the filtration of
  `V(m)` are the pullbacks of those of `V ⊗ ℤ(m)` along the inverse right unitor.
* `TauCeti.Hodge.HodgeStructureOn.tensorProduct_tate_hodgeNumber`: the Hodge numbers of
  `V ⊗ ℤ(m)` are those of `V` shifted by `m`.
* `TauCeti.Hodge.tate_add_F_eq_comap`: the Hodge filtration of `ℤ(k + m)` is the pullback of that
  of `ℤ(k) ⊗ ℤ(m)` along the inverse right unitor.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

namespace Conjugation

/-- The inverse right unitor `W ≃ₗ[ℂ] W ⊗[ℂ] ℂ` intertwines a conjugation `ω` of `W` with the
tensor product of `ω` and the conjugation of the Tate complexification `ℂ`. -/
theorem rid_symm_map_conj (ω : Conjugation W) (x : W) :
    (TensorProduct.rid ℂ W).symm (ω.toEquiv x) =
      (ω.tensorProduct (latticeConjugation isBaseChange_tateLatticeMap)).toEquiv
        ((TensorProduct.rid ℂ W).symm x) := by
  simp [TensorProduct.rid_symm_apply, tensorProduct_toEquiv_tmul, latticeConj_tateLatticeMap]

end Conjugation

namespace HodgeStructureOn

variable {ω : Conjugation W} {n : ℤ}

/-- Every Hodge component of `V ⊗ ℤ(m)` is carried by the right unitor into the component of `V`
of degree shifted by `m`. -/
private theorem tensorProduct_tate_piece_le_comap (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tensorProduct (tate m)).piece p ≤
      (hs.piece (p + m)).comap (TensorProduct.rid ℂ W).toLinearMap := by
  rw [tensorProduct_piece_eq_iSup]
  refine iSup_le fun r ↦ Submodule.map₂_le.mpr fun x hx z hz ↦ ?_
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, TensorProduct.mk_apply, TensorProduct.rid_tmul]
  rw [tate_piece] at hz
  split_ifs at hz with hr
  · -- The Tate factor lies in `H^{-m,-m}`, so the degree of `x` is exactly `p + m`.
    rw [show p + m = r by omega]
    exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hz
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

/-- **The Tate twist is the tensor product with `ℤ(m)`: components.** The degree-`p` component
of `V(m)` is the pullback of the degree-`p` component of `V ⊗ ℤ(m)` along the inverse right
unitor `W ≃ₗ[ℂ] W ⊗[ℂ] ℂ`. -/
theorem tateTwist_piece_eq_comap (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).piece p =
      ((hs.tensorProduct (tate m)).piece p).comap (TensorProduct.rid ℂ W).symm.toLinearMap := by
  have hpiece : ∀ q, ((hs.tensorProduct (tate m)).comap (TensorProduct.rid ℂ W).symm
      ω.rid_symm_map_conj).piece q ≤ (hs.tateTwist m).piece q := by
    intro q x hx
    rw [comap_piece] at hx
    have hmem := tensorProduct_tate_piece_le_comap hs m q hx
    rwa [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ← tateTwist_piece] at hmem
  rw [← congrFun (((hs.tateTwist m).piece_iSupIndep.le_iff_eq_of_iSup_eq_top
    ((hs.tensorProduct (tate m)).comap (TensorProduct.rid ℂ W).symm
      ω.rid_symm_map_conj).iSup_piece_eq_top).mp hpiece) p, comap_piece]

/-- **The Tate twist is the tensor product with `ℤ(m)`: filtration.** The filtration step
`F^p(V(m)) = F^{p+m}(V)` is the pullback of the step `F^p(V ⊗ ℤ(m))` along the inverse right
unitor `W ≃ₗ[ℂ] W ⊗[ℂ] ℂ`. -/
theorem tateTwist_F_eq_comap (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).F p =
      ((hs.tensorProduct (tate m)).F p).comap (TensorProduct.rid ℂ W).symm.toLinearMap := by
  rw [(hs.tateTwist m).F_eq_iSup_piece p, (hs.tensorProduct (tate m)).F_eq_iSup_piece p,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, Submodule.map_iSup]
  refine iSup_congr fun q ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [hs.tateTwist_piece_eq_comap m q, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]

/-- The Hodge numbers of `V ⊗ ℤ(m)` are those of `V` shifted by `m`. -/
@[simp]
theorem tensorProduct_tate_hodgeNumber (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tensorProduct (tate m)).hodgeNumber p = hs.hodgeNumber (p + m) := by
  rw [← tateTwist_hodgeNumber, hodgeNumber_def, hodgeNumber_def, tateTwist_piece_eq_comap,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, LinearEquiv.finrank_map_eq]

end HodgeStructureOn

/-- The Hodge filtration of the Tate structure `ℤ(k + m)` is the pullback of that of
`ℤ(k) ⊗ ℤ(m)` along the inverse right unitor `ℂ ≃ₗ[ℂ] ℂ ⊗[ℂ] ℂ`. -/
theorem tate_add_F_eq_comap (k m p : ℤ) :
    (tate (k + m)).F p =
      (((tate k).tensorProduct (tate m)).F p).comap (TensorProduct.rid ℂ ℂ).symm.toLinearMap := by
  rw [← HodgeStructureOn.tateTwist_F_eq_comap, HodgeStructureOn.tateTwist_F, tate_F, tate_F]
  have hiff : p ≤ -(k + m) ↔ p + m ≤ -k := by omega
  simp only [hiff]

end TauCeti.Hodge
