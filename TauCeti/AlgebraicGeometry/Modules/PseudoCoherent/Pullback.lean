/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Flat

/-!
# Flat pullback of pseudo-coherent sheaves

Pullback along a flat morphism preserves finite free resolutions and hence pseudo-coherent
module sheaves. No Noetherian or finiteness hypothesis on the morphism is required. The
resolutions may be unbounded: the argument preserves exactness in every positive degree,
not just a finite presentation.

Flatness is used only on the short complexes of finite free resolving terms, which are
quasi-coherent, to preserve exactness in positive degrees. Degree zero uses only right
exactness of pullback to preserve the cokernel presentation of the augmentation. Restriction
of pullback to an inverse-image open then gives the local result.

## References

* The Stacks Project, Section 36.10 (Tag 08E4), pseudo-coherent complexes on schemes.
* The Stacks Project, Lemma 15.66.13 (Tag 066C), flat base change of pseudo-coherence.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} {M : Y.Modules}

/-- Flat pullback carries a resolution by finite free module sheaves to such a resolution.
The resolution need not terminate. -/
theorem HasFiniteFreeResolution.pullback (h : M.HasFiniteFreeResolution)
    (f : X ⟶ Y) [Flat f] : ((pullback f).obj M).HasFiniteFreeResolution := by
  obtain ⟨P, π, hP, hπ⟩ := hasFiniteFreeResolution_iff.mp h
  have : PreservesColimits (Modules.pullback f) :=
    (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hfree (n : ℕ) : (P.X n).IsQuasicoherent := by
    obtain ⟨ι, _, ⟨e⟩⟩ := hP n
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm inferInstance
  let Q : ChainComplex X.Modules ℕ :=
    ((Modules.pullback f).mapHomologicalComplex (ComplexShape.down ℕ)).obj P
  let ε := (Modules.pullback f).map (π.f 0)
  have hε : Q.d 1 0 ≫ ε = 0 :=
    ((Modules.pullback f).map_comp _ _).symm.trans
      (by rw [← π.comm 1 0, single_obj_d, comp_zero, Functor.map_zero])
  let ρ : Q ⟶ (ChainComplex.single₀ X.Modules).obj ((Modules.pullback f).obj M) :=
    (Q.toSingle₀Equiv _).symm ⟨ε, hε⟩
  have hρ : ρ.f 0 = ε := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  refine hasFiniteFreeResolution_iff.mpr ⟨Q, ρ, fun n ↦ ?_, ⟨fun n ↦ ?_⟩⟩
  · obtain ⟨ι, hι, ⟨e⟩⟩ := hP n
    exact ⟨ι, hι, ⟨(Modules.pullback f).mapIso e ≪≫
      SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom ι⟩⟩
  · cases n with
    | zero =>
      -- Right exactness preserves the cokernel presentation of the augmentation.
      exact P.quasiIsoAt₀_of_map π (Modules.pullback f) ρ hρ
    | succ n =>
      -- In positive degrees both adjacent resolving terms are quasi-coherent.
      rw [quasiIsoAt_iff_exactAt' ρ (n + 1) (ChainComplex.exactAt_succ_single_obj _ _),
        exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      have hexact : P.ExactAt (n + 1) :=
        (exactAt_iff_of_quasiIsoAt π (n + 1)).mpr (ChainComplex.exactAt_succ_single_obj _ _)
      have : (P.sc' (n + 2) (n + 1) n).X₂.IsQuasicoherent := hfree (n + 1)
      have : (P.sc' (n + 2) (n + 1) n).X₃.IsQuasicoherent := hfree n
      exact f.exact_map_pullback_of_flat _
        ((exactAt_iff' P (n + 2) (n + 1) n (by simp) (by simp)).mp hexact)

/-- Pullback along a flat morphism preserves pseudo-coherence of module sheaves on arbitrary
schemes. -/
theorem IsPseudoCoherent.pullback (h : M.IsPseudoCoherent) (f : X ⟶ Y) [Flat f] :
    ((pullback f).obj M).IsPseudoCoherent := by
  apply isPseudoCoherent_iff.mpr
  intro x
  obtain ⟨U, hx, hU⟩ := isPseudoCoherent_iff.mp h (f x)
  have e := (restrictPullbackIso f U (f ⁻¹ᵁ U) le_rfl).app M
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at e
  exact ⟨f ⁻¹ᵁ U, hx, (hU.pullback (f ∣_ U)).of_iso e.symm⟩

end

end AlgebraicGeometry.Scheme.Modules
