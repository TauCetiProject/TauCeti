/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution

/-!
# Transport of Cartan involutions

`TauCeti.twistedRealPoints_conj` identifies the twisted real points of conjugate
automorphisms by precomposition on complex points.
`TauCeti.isCartanInvolution_conj_iff` then transports the Cartan condition using
`TauCeti.PointTopology.isEmbedding_comap_of_surjective`.

See J. S. Milne, *Introduction to Shimura varieties*, §1, definition (9).
-/

public section

open CategoryTheory

namespace TauCeti

open scoped PointTopology

variable {H K : CommHopfAlgCat ℝ}

/-- The twisted real points of a conjugate automorphism correspond under precomposition
with the coordinate Hopf-algebra isomorphism. -/
theorem twistedRealPoints_conj (e : H ≅ K) (θ : H ≅ H) :
    twistedRealPoints (e.symm ≪≫ θ ≪≫ e) =
      (fun p : K →ₐ[ℝ] ℂ ↦ p.comp (e.hom.hom : H →ₐ[ℝ] K)) ⁻¹' twistedRealPoints θ := by
  have hsurj : Function.Surjective e.hom.hom := (CommHopfAlgCat.ofIso e).surjective
  have hcomm : e.hom ≫ (e.symm ≪≫ θ ≪≫ e).hom = θ.hom ≫ e.hom := by simp
  have hcomm_apply (x : H) :
      (e.symm ≪≫ θ ≪≫ e).hom.hom (e.hom.hom x) = e.hom.hom (θ.hom.hom x) := by
    simpa only [CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using
      DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom hcomm) x
  ext p
  simp only [Set.mem_preimage, mem_twistedRealPoints_iff, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, ← hcomm_apply]
  exact hsurj.forall

/-- Conjugation by a real coordinate Hopf-algebra isomorphism preserves and reflects the
Cartan involution condition. -/
@[simp]
theorem isCartanInvolution_conj_iff (e : H ≅ K) {θ : H ≅ H} :
    IsCartanInvolution (e.symm ≪≫ θ ≪≫ e) ↔ IsCartanInvolution θ := by
  rw [isCartanInvolution_iff_isCompact, isCartanInvolution_iff_isCompact,
    twistedRealPoints_conj]
  have hsquare :
      (e.symm ≪≫ θ ≪≫ e).hom ≫ (e.symm ≪≫ θ ≪≫ e).hom = 𝟙 K ↔
        θ.hom ≫ θ.hom = 𝟙 H := by grind
  have hcompact :
      IsCompact ((fun p : K →ₐ[ℝ] ℂ ↦ p.comp (e.hom.hom : H →ₐ[ℝ] K)) ⁻¹'
        twistedRealPoints θ) ↔ IsCompact (twistedRealPoints θ) := by
    let f := (CommHopfAlgCat.ofIso e).toAlgEquiv
    have hf : (f : H →ₐ[ℝ] K) = e.hom.hom.toAlgHom :=
      AlgHom.ext (CommHopfAlgCat.ofIso_apply e)
    rw [← hf]
    have hemb := PointTopology.isEmbedding_comap_of_surjective (R := ℂ) f.toAlgHom f.surjective
    refine hemb.isInducing.isCompact_preimage_iff ?_
    intro p _
    refine ⟨p.comp f.symm.toAlgHom, ?_⟩
    simp only [AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id]
  rw [hsquare, hcompact]

end TauCeti
