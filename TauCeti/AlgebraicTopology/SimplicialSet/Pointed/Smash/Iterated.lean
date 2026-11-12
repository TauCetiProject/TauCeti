/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Smash.Power
public import TauCeti.CategoryTheory.Category.Pointed.Smash.Iterated

-- The degreewise bijectivity proof compares the transported simplicial smash power
-- with the smash power of pointed types.
import all TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Smash.Power
import all TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic
import all TauCeti.CategoryTheory.Category.Pointed.Smash.Power
import all TauCeti.CategoryTheory.Category.Pointed.Smash.Iterated

/-!
# Block coordinates for iterated simplicial smash powers

The isomorphism `(X^∧κ)^∧ι ≅ X^∧(ι × κ)` flattens nested smash powers, with the
outer coordinate first. It is natural in `X`, intertwines permutations of both indices,
and carries concatenation of outer blocks to concatenation of flattened coordinates.
No nonemptiness assumption on either index is needed.

For simplicial spheres it gives `(S^k)^∧n ≅ S^(n*k)`, with lexicographically ordered
coordinates: `(a,b)` has index `a*k+b`. The symmetric-group action permutes entire
blocks. These are the coordinate identifications used for sphere-indexed spectra.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, Section 1.
* S. Schwede, *Symmetric spectra*, Chapter I.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti.PointedSSet

variable {X Y : PointedSSet.{u}} {ι κ ι' κ' μ : Type} {n : SimplexCategoryᵒᵖ}

/-- Group smash coordinates into blocks, indexed by the first coordinate. -/
noncomputable def smashPowCurry (X : PointedSSet.{u}) (ι κ : Type) :
    X.smashPow (ι × κ) ⟶ (X.smashPow κ).smashPow ι :=
  smashPowLift (fun _ f ↦ smashPowMk fun i ↦ smashPowMk fun j ↦ f (i, j))
    (fun _ _ p hp ↦ smashPowMk_eq_point_iff.2
      ⟨p.1, smashPowMk_eq_point_iff.2 ⟨p.2, hp⟩⟩)
    (fun _ _ _ _ ↦ by simp [Function.comp_def])

@[simp]
lemma smashPowCurry_app_smashPowMk (f : ι × κ → X.right.obj n) :
    (smashPowCurry X ι κ).right.app n (smashPowMk f) =
      smashPowMk (fun i ↦ smashPowMk fun j ↦ f (i, j)) :=
  smashPowLift_app_smashPowMk _ _ _ f

instance : IsIso (smashPowCurry X ι κ) := by
  apply (isIso_iff_of_reflects_iso _ (Under.forget _)).1
  suffices ∀ n, IsIso (((Under.forget _).map (smashPowCurry X ι κ)).app n) from
    NatIso.isIso_of_isIso_app _
  intro n
  apply (isIso_iff_bijective _).2
  exact Pointed.smashPow.curry_bijective

/-- Flatten an iterated smash power; the outer coordinate labels blocks. -/
noncomputable def smashPowProdIso (X : PointedSSet.{u}) (ι κ : Type) :
    (X.smashPow κ).smashPow ι ≅ X.smashPow (ι × κ) :=
  (asIso (smashPowCurry X ι κ)).symm

@[simp]
lemma smashPowProdIso_inv : (smashPowProdIso X ι κ).inv = smashPowCurry X ι κ := (rfl)

@[simp]
lemma smashPowProdIso_hom_app_smashPowMk (f : ι → κ → X.right.obj n) :
    (smashPowProdIso X ι κ).hom.right.app n (smashPowMk fun i ↦ smashPowMk (f i)) =
      smashPowMk (Function.uncurry f) := by
  have : IsIso ((smashPowCurry X ι κ).right.app n) :=
    inferInstanceAs (IsIso (((Under.forget _).map (smashPowCurry X ι κ)).app n))
  apply (ConcreteCategory.bijective_of_isIso ((smashPowCurry X ι κ).right.app n)).injective
  exact (ConcreteCategory.congr_hom
    (congr_app (congrArg Under.Hom.right (smashPowProdIso X ι κ).hom_inv_id) n) _).trans
      (smashPowCurry_app_smashPowMk (Function.uncurry f)).symm

/-- Grouping coordinates commutes with applying a based simplicial map. -/
@[reassoc]
lemma smashPowMap_comp_smashPowCurry (f : X ⟶ Y) :
    smashPowMap f (ι × κ) ≫ smashPowCurry Y ι κ =
      smashPowCurry X ι κ ≫ smashPowMap (smashPowMap f κ) ι := by
  ext n g
  simp [Function.comp_def]

/-- Flattening iterated smash powers is natural in the pointed simplicial set. -/
@[reassoc]
lemma smashPowProdIso_hom_naturality (f : X ⟶ Y) :
    smashPowMap (smashPowMap f κ) ι ≫ (smashPowProdIso Y ι κ).hom =
      (smashPowProdIso X ι κ).hom ≫ smashPowMap f (ι × κ) := by
  apply (cancel_epi (smashPowProdIso X ι κ).inv).1
  apply (cancel_mono (smashPowProdIso Y ι κ).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  simpa only [smashPowProdIso_inv] using
    (smashPowMap_comp_smashPowCurry (ι := ι) (κ := κ) f).symm

/-- Empty outer blocks give the same smash unit before and after grouping. -/
@[reassoc (attr := simp)]
lemma smashPowCurry_comp_smashPowToUnit [IsEmpty ι] :
    smashPowCurry X ι κ ≫ smashPowToUnit (X.smashPow κ) ι =
      smashPowToUnit X (ι × κ) := by
  ext n f
  simp

/-- Reindexing the flattened coordinates groups into the reindexings within and between
blocks. In particular, taking the inner reindexing to be the identity permutes whole blocks. -/
@[reassoc]
lemma smashPowReindex_comp_smashPowCurry (e : ι ≃ ι') (d : κ ≃ κ') :
    X.smashPowReindex (Equiv.prodCongr e d) ≫ smashPowCurry X ι' κ' =
      smashPowCurry X ι κ ≫ smashPowMap (X.smashPowReindex d) ι ≫
        (X.smashPow κ').smashPowReindex e := by
  ext n g
  simp [Function.comp_def]

/-- Grouping coordinates preserves concatenation of blocks. The distributivity bijection
retains the outer block order and leaves the inner coordinate unchanged. -/
@[reassoc]
lemma smashPowAppend_comp_smashPowCurry :
    smashPowAppend X (ι × κ) (μ × κ) ≫
        X.smashPowReindex (Equiv.sumProdDistrib ι μ κ).symm ≫
        smashPowCurry X (ι ⊕ μ) κ =
      (smashPowCurry X ι κ ⊗ₘ smashPowCurry X μ κ) ≫
        smashPowAppend (X.smashPow κ) ι μ := by
  apply smashPow_tensor_hom_ext
  intro n f g
  simp only [comp_right_app_apply, smashPowAppend_app_smashMk,
    smashPowReindex_app_smashPowMk, Equiv.symm_symm, smashPowCurry_app_smashPowMk,
    tensorHom_app_smashMk]
  congr 1
  funext i
  cases i <;> rfl

/-! ### Simplicial spheres -/

/-- Flatten `n` ordered blocks of `k` circle coordinates. The coordinate `(a,b)` is
numbered `a*k+b`, so the block index precedes the coordinate within the block. -/
noncomputable def sphereSmashPowIso (k n : ℕ) :
    (sphere k).smashPow (Fin n) ≅ sphere (n * k) :=
  smashPowProdIso circle (Fin n) (Fin k) ≪≫ circle.smashPowReindexIso finProdFinEquiv

@[simp]
lemma sphereSmashPowIso_hom_app_smashPowMk {k r : ℕ}
    (f : Fin r → Fin k → circle.right.obj n) :
    (sphereSmashPowIso k r).hom.right.app n (smashPowMk fun i ↦ smashPowMk (f i)) =
      smashPowMk (Function.uncurry f ∘ finProdFinEquiv.symm) := by
  simp [sphereSmashPowIso]

@[simp]
lemma sphereSmashPowIso_inv_app_smashPowMk {k r : ℕ}
    (f : Fin (r * k) → circle.right.obj n) :
    (sphereSmashPowIso k r).inv.right.app n (smashPowMk f) =
      smashPowMk (fun i ↦ smashPowMk fun j ↦ f (finProdFinEquiv (i, j))) := by
  simp [sphereSmashPowIso, Function.comp_def]

/-- Flattening carries the permutation of `r` sphere blocks to the permutation of
`r*k` circle coordinates induced by `(a,b) ↦ (e a,b)`. -/
@[reassoc]
lemma sphereSmashPowIso_hom_block_permutation (k r : ℕ) (e : Equiv.Perm (Fin r)) :
    (sphere k).smashPowReindex e ≫ (sphereSmashPowIso k r).hom =
      (sphereSmashPowIso k r).hom ≫ circle.smashPowReindex
        ((finProdFinEquiv.symm.trans (Equiv.prodCongr e (Equiv.refl (Fin k)))).trans
          finProdFinEquiv) := by
  apply (cancel_mono (sphereSmashPowIso k r).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (sphereSmashPowIso k r).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- Compare on flattened families, so even zero-length blocks need no chosen coordinate.
  ext n f
  simp only [sphereSmashPowIso, Iso.trans_inv, smashPowReindexIso_inv,
    smashPowProdIso_inv, comp_right_app_apply, smashPowReindex_app_smashPowMk,
    smashPowCurry_app_smashPowMk, Function.comp_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Prod.map_apply]
  rfl

end TauCeti.PointedSSet
