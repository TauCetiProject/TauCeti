/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Strongly sheafy Huber rings

Hansen and Kedlaya call a Huber ring `A` *strongly sheafy* when every completed restricted
power-series algebra `A⟨X₁, …, Xₙ⟩`, `n ≥ 0`, is sheafy. Sheafiness of `A` alone is not known to
pass to finite étale `A`-algebras (Kedlaya–Liu, Remark 8.2.18); strong sheafiness is the stronger
hypothesis Hansen and Kedlaya introduce so that sheafiness survives the constructions of étale
geometry. It contains the strongly noetherian Tate rings and the stably sheafy rings.

The definition is stated for an arbitrary Huber ring. Since `A⟨X₁, …, Xₙ⟩` is formed through the
separated completion, it only depends on the completion of `A`, and so does strong sheafiness.

## Main definitions

* `TauCeti.Huber.IsStronglySheafy`: every `A⟨X₁, …, Xₙ⟩` is sheafy
  (`TauCeti.Huber.IsSheafyRing`).

## Main results

* `TauCeti.Huber.IsStronglySheafy.isSheafyRing`: a strongly sheafy ring is sheafy, the case
  `n = 0`.
* `TauCeti.Huber.IsStronglySheafy.restrictedMvPowerSeriesCompletion`: `A⟨X₁, …, Xₘ⟩` is strongly
  sheafy when `A` is, by the iteration isomorphism `A⟨X₁, …, Xₘ⟩⟨Y₁, …, Yₙ⟩ ≅ A⟨X, Y⟩`.
* `IsDenseInducing.isStronglySheafy_iff`, `TauCeti.Huber.isStronglySheafy_congr` and
  `TauCeti.Huber.isStronglySheafy_completion_iff`: strong sheafiness is invariant under dense
  inducing ring maps, under isomorphisms of topological rings, and under completion.
* `TauCeti.Huber.IsStronglySheafy.of_isStronglyNoetherian`: strongly noetherian Tate rings, in
  particular complete nonarchimedean fields and their affinoid algebras, are strongly sheafy.
* `TauCeti.Huber.IsStronglySheafy.of_isStablySheafyRing`: stably sheafy rings are strongly
  sheafy, each `A⟨X₁, …, Xₙ⟩` being topologically of finite type over `Â`.

## References

* [D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*], §4, Definition 4.1.
* [K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*], §8.2, Remark 8.2.18.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.26.
-/

public section

open UniformSpace

namespace TauCeti.Huber

universe u

section Definition

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **Hansen–Kedlaya, Definition 4.1**: a Huber ring `A` is *strongly sheafy* when every completed
restricted power-series algebra `A⟨X₁, …, Xₙ⟩`, `n ≥ 0`, is sheafy in the sense of
`TauCeti.Huber.IsSheafyRing`. -/
def IsStronglySheafy : Prop :=
  ∀ n : ℕ, IsSheafyRing (restrictedMvPowerSeriesCompletion n A)

variable {A}

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsStronglySheafy`. -/
theorem isStronglySheafy_iff :
    IsStronglySheafy A ↔ ∀ n : ℕ, IsSheafyRing (restrictedMvPowerSeriesCompletion n A) :=
  (Iff.rfl)

/-- **`A⟨X₁, …, Xₘ⟩` is strongly sheafy when `A` is**: its restricted power-series algebras
`A⟨X₁, …, Xₘ⟩⟨Y₁, …, Yₙ⟩` are, as topological rings, the algebras `A⟨X₁, …, Xₘ, Y₁, …, Yₙ⟩`
(`TauCeti.Huber.iterateRingEquiv`). -/
theorem IsStronglySheafy.restrictedMvPowerSeriesCompletion (h : IsStronglySheafy A) (m : ℕ) :
    IsStronglySheafy (restrictedMvPowerSeriesCompletion m A) := fun n ↦
  (isSheafyRing_iff_of_ringEquiv _
    (continuous_iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ rfl) fun _ ↦ by simp [Completion.coe_one])
    (continuous_iterateRingEquiv_symm ..)).mp (isStronglySheafy_iff.mp h (m + n))

end Definition

/-! ### Transport -/

section Transport

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- **Strong sheafiness is invariant under a dense inducing ring map**: if `φ : A → B` is dense
inducing, then `A` is strongly sheafy exactly when `B` is. -/
-- The completed restricted power-series algebras over `A` and over `B` are isomorphic as
-- topological rings, by `IsDenseInducing.restrictedMvPowerSeriesCompletionEquiv`.
theorem _root_.IsDenseInducing.isStronglySheafy_iff {φ : A →+* B} (hφ : IsDenseInducing φ) :
    IsStronglySheafy A ↔ IsStronglySheafy B :=
  forall_congr' fun _ ↦ isSheafyRing_iff_of_ringEquiv _
    hφ.continuous_restrictedMvPowerSeriesCompletionEquiv
    hφ.continuous_restrictedMvPowerSeriesCompletionEquiv_symm

/-- **Strong sheafiness is invariant under isomorphisms of topological rings.** -/
theorem isStronglySheafy_congr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsStronglySheafy A ↔ IsStronglySheafy B :=
  IsDenseInducing.isStronglySheafy_iff (φ := (e : A →+* B))
    (Homeomorph.mk e.toEquiv he he').isDenseEmbedding.isDenseInducing

end Transport

/-! ### Uniform Huber rings -/

section Uniform

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **Strong sheafiness is invariant under completion**: the completion `Â` of a Huber ring `A` is
strongly sheafy exactly when `A` is. -/
@[simp]
theorem isStronglySheafy_completion_iff : IsStronglySheafy (Completion A) ↔ IsStronglySheafy A :=
  (Completion.isDenseInducing_coe.isStronglySheafy_iff (φ := Completion.coeRingHom)).symm

/-- **A strongly sheafy Huber ring is sheafy**: this is the case `n = 0` of the definition, since
`A⟨⟩` is the completion of the ring `A` of power series in no variables. -/
theorem IsStronglySheafy.isSheafyRing (h : IsStronglySheafy A) : IsSheafyRing A :=
  (isSheafyRing_iff_of_ringEquiv _ (continuous_weightedRestrictedSubringFinZeroEquiv _)
    (continuous_weightedRestrictedSubringFinZeroEquiv_symm _)).mp
    (isSheafyRing_completion_iff.mp (isStronglySheafy_iff.mp h 0))

/-- **Stably sheafy Huber rings are strongly sheafy**: each `A⟨X₁, …, Xₙ⟩` is a complete Hausdorff
Huber ring topologically of finite type over `Â`, presented by `Â⟨X₁, …, Xₙ⟩ ≅ A⟨X₁, …, Xₙ⟩`. -/
theorem IsStronglySheafy.of_isStablySheafyRing (h : IsStablySheafyRing.{u, u} A) :
    IsStronglySheafy A := fun n ↦ by
  let e := IsDenseInducing.restrictedMvPowerSeriesCompletionEquiv
    (φ := (Completion.coeRingHom : A →+* Completion A)) n Completion.isDenseInducing_coe
  have he : IsOpenQuotientMap e.symm := (Homeomorph.mk e.symm.toEquiv
    (IsDenseInducing.continuous_restrictedMvPowerSeriesCompletionEquiv_symm ..)
    (IsDenseInducing.continuous_restrictedMvPowerSeriesCompletionEquiv ..)).isOpenQuotientMap
  exact isStablySheafyRing_iff.mp h _ _
    ((isStrictlyTopologicallyFiniteType_algebraMap n).comp_isOpenQuotientMap
      (ψ := (e.symm : _ →+* _)) he).isTopologicallyFiniteType

end Uniform

/-! ### Strongly noetherian Tate rings -/

/-- **Strongly noetherian Tate rings are strongly sheafy**: each `A⟨X₁, …, Xₙ⟩` is again a
strongly noetherian Tate ring, hence sheafy by Wedhorn's Theorem 8.28(b)
(`TauCeti.Huber.isSheafyRing_of_isStronglyNoetherian`). `A` need not be complete or Hausdorff. -/
theorem IsStronglySheafy.of_isStronglyNoetherian {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A] : IsStronglySheafy A :=
  fun _ ↦ isSheafyRing_of_isStronglyNoetherian

end TauCeti.Huber

end
