/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.IdealTorsion
public import TauCeti.RepresentationTheory.QuotSMulTop
public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Category
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import TauCeti.Algebra.Module.Torsion.IsomorphismCriterion
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.AdicCompletion.Pow

/-!
# Uniformizer-adically admissible representations

Let `A` be a local coefficient ring with maximal ideal `𝔪`, and let `ϖ : A` be the image
of a uniformizer of the coefficient DVR. Emerton's uniformizer-adically admissible
representations are complete for `(ϖ)` and have bounded `ϖ`-power torsion. Each reduction
`V / ϖⁿ V` is smooth and every vector in it is killed by a power of `𝔪`. Admissibility
is imposed on the socle `(V / ϖ V)[𝔪]` over the residue field. For locally profinite groups
smoothness means precisely that every vector is fixed by some compact open subgroup.

`TauCeti.UniformizerAdmissibleRep` is the full subcategory with these objects. It has
reduction functors and a residual-socle functor. For a morphism between torsion-free
lattices that becomes bijective after inverting `ϖ`, injectivity of its image under the
residual-socle functor detects whether it is an isomorphism.

## References

* M. Emerton, *Local-global compatibility in the p-adic Langlands programme for GL₂/ℚ*,
  draft of 23 March 2011, Definition 3.1.1 and Lemma 3.1.6. The isomorphism criterion
  uses bijectivity after inverting the uniformizer to ensure a torsion cokernel.
-/

public section

open CategoryTheory IsLocalRing Representation Submodule

universe w u v

variable {A : Type u} [CommRing A] [IsLocalRing A] {G : Type v} [Group G] [TopologicalSpace G]

namespace Representation

variable {V : Type w} [AddCommGroup V] [Module A V]

/-- Emerton's uniformizer-adic admissibility conditions for an action over a local coefficient
ring. The parameter `ϖ` is the image in `A` of the coefficient uniformizer. -/
@[mk_iff]
class IsUniformizerAdicallyAdmissible (ρ : Representation A G V) (ϖ : A) : Prop where
  isAdicComplete : IsAdicComplete (Ideal.span {ϖ}) V
  bounded_torsion : ∃ n : ℕ, (Ideal.span {ϖ}).primaryComponent V ≤ torsionBy A V (ϖ ^ n)
  isSmooth_quotSMulTop (n : ℕ) : IsSmooth (ρ.quotSMulTop (ϖ ^ n))
  primaryComponent_eq_top (n : ℕ) : (maximalIdeal A).primaryComponent (QuotSMulTop (ϖ ^ n) V) = ⊤
  isAdmissible_socle : IsAdmissible ((ρ.quotSMulTop ϖ).torsionByIdeal (maximalIdeal A))

/-- The zero representation satisfies the uniformizer-adic admissibility conditions. -/
instance (ρ : Representation A G V) (ϖ : A) [Subsingleton V] :
    ρ.IsUniformizerAdicallyAdmissible ϖ where
  isAdicComplete := inferInstance
  bounded_torsion := ⟨0, (Subsingleton.elim _ _).le⟩
  isSmooth_quotSMulTop _ := inferInstance
  primaryComponent_eq_top _ := Subsingleton.elim _ _
  isAdmissible_socle := inferInstance

/-- For a finite module over a complete Noetherian local ring with `√(ϖ) = 𝔪`, uniformizer-adic
admissibility is equivalent to smoothness of the reductions. This includes a finite lattice over
a complete DVR after a ramified extension of coefficient DVRs. -/
theorem isUniformizerAdicallyAdmissible_iff_of_finite (ρ : Representation A G V) (ϖ : A)
    [IsNoetherianRing A] [Module.Finite A V] [IsAdicComplete (maximalIdeal A) A]
    (hϖ : (Ideal.span {ϖ}).radical = maximalIdeal A) :
    ρ.IsUniformizerAdicallyAdmissible ϖ ↔ ∀ n : ℕ, IsSmooth (ρ.quotSMulTop (ϖ ^ n)) := by
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hϖ.ge (IsNoetherian.noetherian _)
  refine ⟨fun h ↦ h.isSmooth_quotSMulTop, fun hs ↦ ⟨?_, ?_, hs, ?_, ?_⟩⟩
  · have : IsAdicComplete (maximalIdeal A) V := IsAdicComplete.of_finite _ _
    exact IsAdicComplete.of_pow_le_of_pow_le (k := 1)
      (by rw [pow_one, ← hϖ]; exact Ideal.le_radical) he
  · obtain ⟨n, hn⟩ := (Ideal.span {ϖ}).exists_le_torsionBySet_pow_of_le_primaryComponent
      (IsNoetherian.noetherian ((Ideal.span {ϖ}).primaryComponent V)) le_rfl
    exact ⟨n, by simpa [Ideal.span_singleton_pow] using hn⟩
  · intro n
    apply Ideal.primaryComponent_eq_top_of_le_annihilator _ (n := e * n)
    rw [pow_mul]
    apply (Ideal.pow_right_mono he n).trans
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact QuotSMulTop.mem_annihilator _ _
  · have : IsSmooth (ρ.quotSMulTop ϖ) := by
      rw [← pow_one ϖ]
      exact hs 1
    let S := torsionBySet A (QuotSMulTop ϖ V) (maximalIdeal A)
    have : Module.Finite (A ⧸ maximalIdeal A) S := Module.Finite.of_restrictScalars_finite A _ _
    infer_instance

end Representation

namespace TauCeti

/-- The full subcategory of uniformizer-adically admissible representations. Morphisms are
all equivariant `A`-linear maps. -/
abbrev UniformizerAdmissibleRep (A : Type u) [CommRing A] [IsLocalRing A]
    (G : Type v) [Group G] [TopologicalSpace G] (ϖ : A) :=
  ObjectProperty.FullSubcategory (C := Rep.{w} A G) fun V ↦ V.ρ.IsUniformizerAdicallyAdmissible ϖ

namespace UniformizerAdmissibleRep

variable {ϖ : A}

/-- The underlying action of a bundled object satisfies the admissibility conditions. -/
instance (X : UniformizerAdmissibleRep.{w} A G ϖ) :
    X.obj.ρ.IsUniformizerAdicallyAdmissible ϖ :=
  X.property

/-- Bundle a uniformizer-adically admissible action as an object of the full subcategory. -/
abbrev of {V : Type w} [AddCommGroup V] [Module A V] (ρ : Representation A G V) (ϖ : A)
    [h : ρ.IsUniformizerAdicallyAdmissible ϖ] : UniformizerAdmissibleRep A G ϖ :=
  ⟨Rep.of ρ, h⟩

/-- Reduction modulo the `n`th power of the uniformizer, with its smooth action. -/
@[simps! obj_obj map_hom]
noncomputable abbrev reduction (ϖ : A) (n : ℕ) :
    UniformizerAdmissibleRep.{w} A G ϖ ⥤ SmoothRep A G where
  obj X := ⟨Rep.of (X.obj.ρ.quotSMulTop (ϖ ^ n)), X.property.isSmooth_quotSMulTop n⟩
  map f := ObjectProperty.homMk (Rep.ofHom (f.hom.hom.quotSMulTop (ϖ ^ n)))
  map_id _ := ObjectProperty.hom_ext _ (Rep.hom_ext (IntertwiningMap.ext (by simp)))
  map_comp _ _ := ObjectProperty.hom_ext _ (Rep.hom_ext (IntertwiningMap.ext (by simp)))

/-- Reduce modulo the uniformizer and take the maximal-ideal torsion. The resulting smooth
representation has coefficients in the residue field. -/
@[simps! obj_obj map_hom]
noncomputable abbrev residualSocle (ϖ : A) :
    UniformizerAdmissibleRep.{w} A G ϖ ⥤ SmoothRep (A ⧸ maximalIdeal A) G where
  obj X := ⟨Rep.of ((X.obj.ρ.quotSMulTop ϖ).torsionByIdeal (maximalIdeal A)),
    X.property.isAdmissible_socle.toIsSmooth⟩
  map f := ObjectProperty.homMk (Rep.ofHom ((f.hom.hom.quotSMulTop ϖ).torsionByIdeal _))
  map_id _ := ObjectProperty.hom_ext _ (Rep.hom_ext (IntertwiningMap.ext (by simp)))
  map_comp _ _ := ObjectProperty.hom_ext _ (Rep.hom_ext (IntertwiningMap.ext (by simp)))

/-- The residual socle has finite-dimensional invariants under every compact open subgroup. -/
instance (X : UniformizerAdmissibleRep.{w} A G ϖ) :
    IsAdmissible (((residualSocle ϖ).obj X).obj.ρ) :=
  X.property.isAdmissible_socle

/-- An equivariant map between uniformizer-torsion-free objects which becomes bijective
after inverting the uniformizer is an isomorphism exactly when it induces an injection on
residual socles. -/
theorem isIso_iff_injective_residualSocle_map {X Y : UniformizerAdmissibleRep.{w} A G ϖ}
    (f : X ⟶ Y) (hX : IsSMulRegular X.obj ϖ) (hY : IsSMulRegular Y.obj ϖ)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (i : X.obj →ₗ[A] M) (j : Y.obj →ₗ[A] N) [IsLocalizedModule (.powers ϖ) i]
    [IsLocalizedModule (.powers ϖ) j]
    (hloc : Function.Bijective (IsLocalizedModule.map (.powers ϖ) i j f.hom.hom.toLinearMap)) :
    IsIso f ↔ Function.Injective ((residualSocle ϖ).map f).hom.hom.toLinearMap := by
  rw [← isIso_iff_of_reflects_iso f (ObjectProperty.ι _), ConcreteCategory.isIso_iff_bijective]
  have hprimary := X.property.primaryComponent_eq_top 1
  rw [pow_one] at hprimary
  rw [residualSocle_map_hom, Rep.hom_ofHom, IntertwiningMap.toLinearMap_torsionByIdeal,
    IntertwiningMap.toLinearMap_quotSMulTop, LinearMap.injective_torsionByIdeal_iff]
  exact bijective_iff_disjoint_torsionBySet_ker_quotSMulTop_map i j hX hY hloc hprimary

end UniformizerAdmissibleRep

end TauCeti
