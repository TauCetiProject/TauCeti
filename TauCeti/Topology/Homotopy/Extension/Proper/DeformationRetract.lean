/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Proper.Prod
public import TauCeti.Topology.Homotopy.Proper
import TauCeti.Topology.Maps.Proper.Basic

/-!
# A proper cofibration which is a proper homotopy equivalence is a proper strong deformation retract

Let `A ⊆ X` have the proper homotopy extension property. If the subspace inclusion `A → X` is a
proper homotopy equivalence (`ContinuousMap.HasProperHomotopyInverse`), then `A` is closed and is a
*proper strong deformation retract* of `X`: there is a proper retraction `r : C(X, A)` together
with a proper homotopy
`H : (ContinuousMap.id X).HomotopyRel ((ContinuousMap.subtypeVal A).comp r) A` from the identity of
`X` to `r` followed by the inclusion, fixing every point of `A` at all times and jointly proper on
`I × X` (`TauCeti.properStrongDeformationRetract_of_inverse`). Conversely, any closed subset
admitting such a proper strong deformation retraction includes as a proper homotopy equivalence
(`TauCeti.HasProperHomotopyExtensionProperty.hasProperHomotopyInverse_subtypeVal_iff`).

This is the form in which proper cofibrations upgrade proper homotopy equivalences to proper
deformations, paralleling
`TauCeti.HasHomotopyExtensionProperty.exists_strong_deformation_retraction` in the ordinary homotopy
category: when `f : X → Y` is a proper homotopy equivalence, the inclusion of `X` into the mapping
cylinder of `f` has the proper homotopy extension property and has a proper homotopy inverse, so `X`
is a proper strong deformation retract of the mapping cylinder.

No Hausdorff or local compactness assumption on `X` is needed: properness of `Subtype.val : A → X`
is equivalent to `IsClosed A` (`TauCeti.isProperMap_subtypeVal_iff`).

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic`: a proper
  homotopy left inverse of `A ↪ X` is properly homotopic to a proper retraction `r : C(X, A)`.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_homotopyRel_isProperMap_of_retraction`: a
  retraction onto a proper cofibration `A` whose composite with the inclusion is properly homotopic
  to `id_X` admits a proper homotopy relative to `A` from `id_X`.
* `TauCeti.properStrongDeformationRetract_of_inverse`: **rectification of a proper homotopy inverse
  of `A ↪ X` to a proper strong deformation retraction.**
* `TauCeti.HasProperHomotopyExtensionProperty.hasProperHomotopyInverse_subtypeVal_iff`: for a
  subset with the proper homotopy extension property, the inclusion `A ↪ X` is a proper homotopy
  equivalence if and only if `A` is closed and is a proper strong deformation retract of `X`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1 (Theorem 1.6).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Proposition 0.19.
-/

public section

open ContinuousMap Set unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A proper map `g : C(X, A)` whose restriction to `A` is properly homotopic to the identity of `A`
is properly homotopic to a proper retraction `r : C(X, A)` onto `A`, provided `A` has the proper
homotopy extension property. No closedness assumption on `A` is required here. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic
    (hA : HasProperHomotopyExtensionProperty A) (g : C(X, A)) (hg : IsProperMap g)
    (H : (g.comp (subtypeVal A)).Homotopy (ContinuousMap.id A)) (hH : IsProperMap H) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r a = a) ∧
      ∃ G : r.Homotopy g, IsProperMap G := by
  obtain ⟨G₀, hG₀p, hG₀_zero, hG₀_mem⟩ :=
    hA.exists_extension g hg H.toContinuousMap hH fun a ↦ by simp
  let G' : g.Homotopy ⟨fun x ↦ G₀ (1, x), by fun_prop⟩ :=
    { toContinuousMap := G₀, map_zero_left := hG₀_zero, map_one_left := fun _ ↦ rfl }
  refine ⟨⟨fun x ↦ G₀ (1, x), by fun_prop⟩, G'.isProperMap_right hG₀p, fun a ↦ ?_,
    G'.symm, G'.isProperMap_symm hG₀p⟩
  simpa using hG₀_mem 1 a

/-- A retraction `r : C(X, A)` onto a subset `A` with the proper homotopy extension property whose
composite with the inclusion is properly homotopic to the identity of `X` admits a proper homotopy
relative to `A` from the identity of `X` to `(subtypeVal A).comp r`. Both closedness of `A` and
properness of `r` follow automatically from properness of `K`. -/
theorem HasProperHomotopyExtensionProperty.exists_homotopyRel_isProperMap_of_retraction
    (hA : HasProperHomotopyExtensionProperty A) {r : C(X, A)} (hr : ∀ a : A, r a = a)
    (K : ((subtypeVal A).comp r).Homotopy (ContinuousMap.id X)) (hK : IsProperMap K) :
    ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H := by
  let ir : C(X, X) := (subtypeVal A).comp r
  have hir : IsProperMap ir := K.isProperMap_left hK
  have hval : (subtypeVal A : A → X) = Subtype.val := funext (subtypeVal_apply A)
  have hA' : IsClosed A := isProperMap_subtypeVal_iff.1
    (hval ▸ (HasProperHomotopyInverse.of_deformationRetraction
      (fun a ↦ by simpa using hr a) hK).isProperMap)
  let F : (ContinuousMap.id X).Homotopy ir := K.symm
  have hF : IsProperMap F := K.isProperMap_symm hK
  let G : ir.Homotopy ir :=
    (F.symm.compContinuousMap ir).cast
      (ContinuousMap.ext fun x ↦ by simp [ir, hr]) (ContinuousMap.id_comp ir)
  have hG : IsProperMap G := by
    rw [Homotopy.isProperMap_cast_iff]
    exact Homotopy.isProperMap_compContinuousMap (F.isProperMap_symm hF) hir
  -- Run `F` from `id_X` to `incl ∘ r`, followed by `F.symm` precomposed with the proper idempotent
  -- `incl ∘ r`; on `A`, which `r` fixes, the second half retraces the first.
  refine hA.exists_homotopyRel_isProperMap_of_retracing hA' hF hG fun t x hx ↦ ?_
  have hrx : ir x = x := by simp [ir, hr ⟨x, hx⟩]
  simp [G, F, hrx]

/-- **A proper cofibration whose inclusion has a proper homotopy inverse is a proper strong
deformation retract.** Given `A ⊆ X` with the proper homotopy extension property such that the
subspace inclusion `A → X` is proper and admits a homotopy inverse `g : C(X, A)` with jointly
proper homotopies `H : g ∘ incl ≃ id_A` on `I × A` and `K : incl ∘ g ≃ id_X` on `I × X`, there is
a proper retraction `r : C(X, A)` together with a proper homotopy relative to `A` from `id_X` to
`incl ∘ r`. Properness of `g` follows automatically from properness of `K`. -/
theorem properStrongDeformationRetract_of_inverse
    {X : Type u} [TopologicalSpace X]
    (A : Set X) (hA : HasProperHomotopyExtensionProperty A)
    (hincl : IsProperMap (Subtype.val : A → X)) (g : C(X, A))
    (H : ContinuousMap.Homotopy (g.comp (ContinuousMap.subtypeVal A))
      (ContinuousMap.id A))
    (K : ContinuousMap.Homotopy
      ((ContinuousMap.subtypeVal A).comp g) (ContinuousMap.id X))
    (hH : IsProperMap H) (hK : IsProperMap K) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r (a : X) = a) ∧
      ∃ H : (ContinuousMap.id X).HomotopyRel
        ((ContinuousMap.subtypeVal A).comp r) A,
        IsProperMap H := by
  have hval : (subtypeVal A : A → X) = Subtype.val := funext (subtypeVal_apply A)
  have hcomp : Subtype.val ∘ (g : X → A) = ((subtypeVal A).comp g : X → X) := by
    ext x
    simp
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_inj g.continuous continuous_subtypeVal
      (hcomp ▸ K.isProperMap_left hK) Subtype.val_injective
  obtain ⟨r, hrp, hr, G, hGp⟩ := hA.exists_proper_retraction_homotopic g hg H hH
  let K₁ : ((subtypeVal A).comp r).Homotopy ((subtypeVal A).comp g) :=
    (Homotopy.refl (subtypeVal A)).comp G
  have hK₁ : IsProperMap K₁ :=
    Homotopy.isProperMap_comp (Homotopy.isProperMap_refl_iff.2 (hval.symm ▸ hincl)) hGp
  exact ⟨r, hrp, hr, hA.exists_homotopyRel_isProperMap_of_retraction hr
    (K₁.trans K) (K₁.isProperMap_trans hK₁ hK)⟩

/-- **Characterization of proper strong deformation retracts among subsets with the proper homotopy
extension property**: the inclusion `A ↪ X` has a proper homotopy inverse if and only if `A` is
closed and admits a proper strong deformation retraction. -/
theorem HasProperHomotopyExtensionProperty.hasProperHomotopyInverse_subtypeVal_iff
    (hA : HasProperHomotopyExtensionProperty A) :
    (subtypeVal A).HasProperHomotopyInverse ↔
      IsClosed A ∧ ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r a = a) ∧
        ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H := by
  have hval : (subtypeVal A : A → X) = Subtype.val := funext (subtypeVal_apply A)
  refine ⟨fun hf ↦ by
    obtain ⟨g, -, H, K, hH, hK⟩ := hf.exists_inverse
    exact ⟨isProperMap_subtypeVal_iff.1 (hval ▸ hf.isProperMap),
      properStrongDeformationRetract_of_inverse A hA (hval ▸ hf.isProperMap) g H K hH hK⟩,
    fun ⟨_, _, _, hr, H, hH⟩ ↦
      HasProperHomotopyInverse.of_deformationRetraction (fun a ↦ by simpa using hr a)
        (K := H.toHomotopy.symm)
        (H.toHomotopy.isProperMap_symm (by rwa [HomotopyWith.coe_toHomotopy]))⟩

end TauCeti
