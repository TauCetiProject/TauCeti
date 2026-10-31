/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Weakly
public import TauCeti.RingTheory.Etale.IndEtale
import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import TauCeti.Algebra.Category.AlgCat.FilteredColimits
import TauCeti.RingTheory.Flat.Colimit
import TauCeti.RingTheory.Ideal.Pure
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Ind-étale algebras are weakly étale

Filtered colimits of weakly étale algebras are weakly étale. In particular, an ind-étale
algebra has flat multiplication map `S ⊗[R] S → S`, as well as being flat over `R`.
This provides the diagonal-flatness condition used in the pro-étale topology.

The proof tests flatness of the surjective multiplication map on its kernel. Every
kernel element comes from a self-tensor product at one stage, and its product
vanishes at a later stage. The elementwise pure-ideal criterion then passes from that
stage to the colimit. No finite generation, Noetherianity or reducedness is required.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Proposition 2.3.3.
* [Stacks Project, Tag 092N](https://stacks.math.columbia.edu/tag/092N).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Algebra.WeaklyEtale

/-- A filtered colimit of weakly étale algebras is weakly étale. -/
theorem of_isColimit {R : Type u} [CommRing R] {J : Type u} [SmallCategory J]
    [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R} [∀ j, WeaklyEtale R (F.obj j)]
    {c : Cocone F} (hc : IsColimit c) : WeaklyEtale R c.pt := by
  let G := forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)
  -- These forgetful functors retain the original underlying type and scalar action.
  have (j : J) : Module.Flat R ((F ⋙ G).obj j) :=
    inferInstanceAs (Module.Flat R (F.obj j))
  refine ⟨Module.Flat.of_isColimit (isColimitOfPreserves G hc), ?_⟩
  apply (RingHom.flat_iff_forall_exists_eq_mul_of_surjective _
    (fun x ↦ ⟨x ⊗ₜ[R] 1, by simp⟩)).mpr
  intro x hx
  obtain ⟨i, y, rfl⟩ := CommAlgCat.isColimit_exists_tensor_rep hc hc x
  have hy : c.ι.app i (Algebra.TensorProduct.lmul' R y) = c.ι.app i 0 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.lmul'_map_self,
      map_zero] using hx
  obtain ⟨j, f, _, hf⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ hy
  let z := Algebra.TensorProduct.map (F.map f).hom (F.map f).hom y
  have hz : Algebra.TensorProduct.lmul' R z = 0 := by
    simpa only [z, Algebra.TensorProduct.lmul'_map_self, map_zero] using hf
  obtain ⟨w, hw, hzw⟩ :=
    (RingHom.flat_iff_forall_exists_eq_mul_of_surjective _
      (fun x : F.obj j ↦ ⟨x ⊗ₜ[R] 1, by simp⟩)).mp (flat_lmul' R (F.obj j)) z hz
  let m := Algebra.TensorProduct.map (c.ι.app j).hom (c.ι.app j).hom
  have hm : m z = Algebra.TensorProduct.map (c.ι.app i).hom (c.ι.app i).hom y := by
    have h : m.comp (Algebra.TensorProduct.map (F.map f).hom (F.map f).hom) =
        Algebra.TensorProduct.map (c.ι.app i).hom (c.ι.app i).hom := by
      rw [← Algebra.TensorProduct.map_comp, ← CommAlgCat.hom_comp, c.w f]
    exact DFunLike.congr_fun h y
  refine ⟨m w, ?_, ?_⟩
  · simpa only [m, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.lmul'_map_self, map_zero] using congrArg (c.ι.app j).hom hw
  · rw [← hm, ← map_mul, ← hzw]

end Algebra.WeaklyEtale

namespace TauCeti.Algebra.IndEtale

/-- Ind-étale algebras are weakly étale: their multiplication map is flat. -/
instance weaklyEtale {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IndEtale R S] : _root_.Algebra.WeaklyEtale R S := by
  obtain ⟨J, _, _, pres, hD⟩ := IndEtale.ind_etale (R := R) (S := S)
  have (j : J) : _root_.Algebra.WeaklyEtale R (pres.diag.obj j) := by
    have := hD j
    infer_instance
  exact _root_.Algebra.WeaklyEtale.of_isColimit pres.isColimit

end TauCeti.Algebra.IndEtale
