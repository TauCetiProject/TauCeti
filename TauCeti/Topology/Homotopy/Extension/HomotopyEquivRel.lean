/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.Homotopic.Rel
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences relative to subspaces with the homotopy extension property

Let `A ⊆ X` and `B ⊆ Y` be subsets with the homotopy extension property, and let `h : X ≃ₕ Y` be
a homotopy equivalence which restricts to a homeomorphism `e : A ≃ₜ B`. Then `h` is a homotopy
equivalence relative to these subsets: it has a homotopy inverse `g : Y → X` which is `e.symm` on
`B`, such that `g ∘ h` is homotopic to the identity relative to `A` and `h ∘ g` is homotopic to
the identity relative to `B` (`TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel`).
When `e` identifies a common subspace of `X` and `Y`, this is Hatcher's statement that a
homotopy equivalence restricting to the identity of a subspace with the homotopy extension
property in both spaces is a homotopy equivalence relative to it.

The case of base points is the based version: a homotopy equivalence `h` with `h x₀ = y₀`, between
spaces whose base points have the homotopy extension property, has a based homotopy inverse, and
both composites are homotopic to the identities relative to the base points
(`TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`). It upgrades an unbased
homotopy inverse of a based map, such as the one given by Whitehead's theorem, to a based one.

## Proof

The proof follows Hatcher. A homotopy inverse `g` of `h` is first deformed, using the homotopy
extension property of `B`, into a map which is `e.symm` on `B`. The key step is that a self-map
`φ` of `X` fixing `A` pointwise and homotopic to the identity has a left inverse relative to `A`
(`TauCeti.HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel_of_homotopic_id`): extend
the restriction to `A` of a homotopy `H` from `φ` to the identity to a homotopy `K` starting at the
identity of `X`, and let `ψ` be its end. Then `ψ ∘ φ` deforms back along `K` to `φ`, and `H`
deforms `φ` to the identity; on `A` the second homotopy retraces the first, so
`TauCeti.HasHomotopyExtensionProperty.homotopicRel_of_retracing` gives a homotopy relative to `A`.
Applied to `g ∘ h`, this gives a left inverse of `h` relative to `A`
(`TauCeti.HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel`). That left inverse
has in turn a left inverse `h'` relative to `B`; then `h ≃ h' ∘ g ∘ h ≃ h'` relative to `A`, so
`g` is also a right inverse of `h` relative to `B`.

## Main results

* `TauCeti.HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel_of_homotopic_id`: a
  self-map fixing `A` and homotopic to the identity has a left inverse relative to `A`.
* `TauCeti.HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel`: a map restricting to a
  homeomorphism `A ≃ₜ B` which has a left homotopy inverse has one relative to `A`.
* `TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel`: **a homotopy equivalence
  restricting to a homeomorphism `A ≃ₜ B` is a homotopy equivalence relative to `A` and `B`.**
* `TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`: a homotopy
  equivalence preserving base points with the homotopy extension property has a based homotopy
  inverse, with both homotopies relative to the base points.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19 and its proof.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap unitInterval

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y}

/-- **A self-map fixing `A` and homotopic to the identity has a left inverse relative to `A`.**
If `A` has the homotopy extension property and `φ : X → X` fixes every point of `A` and is
homotopic to the identity, then there is `ψ : X → X`, also fixing every point of `A` and
homotopic to the identity, such that `ψ ∘ φ` is homotopic to the identity relative to `A`. -/
theorem HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel_of_homotopic_id
    (hA : HasHomotopyExtensionProperty A) {φ : C(X, X)} (hφ : ∀ x ∈ A, φ x = x)
    (hφ' : φ.Homotopic (ContinuousMap.id X)) :
    ∃ ψ : C(X, X), (∀ x ∈ A, ψ x = x) ∧ ψ.Homotopic (ContinuousMap.id X) ∧
      (ψ.comp φ).HomotopicRel (ContinuousMap.id X) A := by
  obtain ⟨H⟩ := hφ'
  -- Extend the restriction of `H` to `A` to a homotopy `K` starting at the identity of `X`.
  obtain ⟨K, hK₀, hK₁⟩ := hA.exists_extension (ContinuousMap.id X)
    (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap (subtypeVal A)))
    fun a => by simp [hφ a a.2]
  let K' : (ContinuousMap.id X).Homotopy ⟨fun x => K (1, x), by fun_prop⟩ :=
    { toContinuousMap := K
      map_zero_left := hK₀
      map_one_left := fun _ => rfl }
  refine ⟨⟨fun x => K (1, x), by fun_prop⟩, fun x hx => by simpa using hK₁ 1 ⟨x, hx⟩,
    ⟨K'.symm⟩, ?_⟩
  -- `ψ ∘ φ` deforms back along `K` to `φ`, which `H` deforms to the identity. On `A`, where `φ`
  -- is the identity and `K` is `H`, the second homotopy retraces the first.
  have hK' (p : I × X) : K' p = K p := rfl
  refine hA.homotopicRel_of_retracing ((K'.symm.compContinuousMap φ).cast rfl
    (ContinuousMap.id_comp φ)) H fun t x hx => ?_
  simpa [hK', hφ x hx] using (hK₁ t ⟨x, hx⟩).symm

/-- **A left homotopy inverse relative to the subspaces.** Let `A ⊆ X` and `B ⊆ Y` have the
homotopy extension property, and let `f : X → Y` restrict to a homeomorphism `e : A ≃ₜ B`. If `f`
has a left homotopy inverse `g`, then it has a left homotopy inverse `g'`, homotopic to `g`,
which is `e.symm` on `B` and such that `g' ∘ f` is homotopic to the identity relative to `A`. -/
theorem HasHomotopyExtensionProperty.exists_leftInverse_homotopicRel
    (hA : HasHomotopyExtensionProperty A) (hB : HasHomotopyExtensionProperty B) (e : A ≃ₜ B)
    {f : C(X, Y)} (hf : ∀ a : A, f a = e a) {g : C(Y, X)}
    (hg : (g.comp f).Homotopic (ContinuousMap.id X)) :
    ∃ g' : C(Y, X), (∀ b : B, g' b = e.symm b) ∧ g'.Homotopic g ∧
      (g'.comp f).HomotopicRel (ContinuousMap.id X) A := by
  obtain ⟨H⟩ := hg
  -- Deform `g`, following `H` at the points of `B`, to a map `g₁` which is `e.symm` on `B`.
  obtain ⟨G, hG₀, hG₁⟩ := hB.exists_extension g
    (H.toContinuousMap.comp
      ((ContinuousMap.id I).prodMap ((subtypeVal A).comp (e.symm : C(B, A)))))
    fun b => by simp [hf]
  let g₁ : C(Y, X) := ⟨fun y => G (1, y), by fun_prop⟩
  have hg₁ (b : B) : g₁ b = e.symm b := (hG₁ 1 b).trans (by simp)
  have hgg₁ : g.Homotopic g₁ :=
    ⟨{ toContinuousMap := G
       map_zero_left := hG₀
       map_one_left := fun _ => rfl }⟩
  -- `g₁ ∘ f` fixes `A` and is homotopic to the identity, so it has a left inverse `ψ`
  -- relative to `A`.
  obtain ⟨ψ, hψA, hψ, hψφ⟩ := hA.exists_leftInverse_homotopicRel_of_homotopic_id
    (φ := g₁.comp f) (fun x hx => by simp [hf ⟨x, hx⟩, hg₁])
    ((hgg₁.symm.comp (.refl f)).trans ⟨H⟩)
  refine ⟨ψ.comp g₁, fun b => by simp [hg₁, hψA _ (e.symm b).2], ?_, ?_⟩
  · simpa using hψ.comp hgg₁.symm
  · rwa [ContinuousMap.comp_assoc]

/-- **A homotopy equivalence under cofibrations is a homotopy equivalence relative to the
subspaces.** Let `A ⊆ X` and `B ⊆ Y` have the homotopy extension property, and let `h : X ≃ₕ Y`
restrict to a homeomorphism `e : A ≃ₜ B`. Then `h` has a homotopy inverse `g`, which is
`e.symm` on `B`, such that `g ∘ h` is homotopic to the identity relative to `A` and `h ∘ g` is
homotopic to the identity relative to `B`. -/
theorem HasHomotopyExtensionProperty.exists_inverse_homotopicRel
    (hA : HasHomotopyExtensionProperty A) (hB : HasHomotopyExtensionProperty B) (h : X ≃ₕ Y)
    (e : A ≃ₜ B) (he : ∀ a : A, h a = e a) :
    ∃ g : C(Y, X), (∀ b : B, g b = e.symm b) ∧
      (g.comp h.toFun).HomotopicRel (ContinuousMap.id X) A ∧
      (h.toFun.comp g).HomotopicRel (ContinuousMap.id Y) B := by
  -- A left inverse `g` of `h` relative to `A`, which is still a homotopy inverse of `h`.
  obtain ⟨g, hgB, hgh, hgf⟩ := hA.exists_leftInverse_homotopicRel hB e he h.left_inv
  -- A left inverse `f'` of `g` relative to `B`.
  obtain ⟨f', -, -, hfg⟩ := hB.exists_leftInverse_homotopicRel hA e.symm (f := g) hgB
    (((Homotopic.refl h.toFun).comp hgh).trans h.right_inv)
  -- Then `h ≃ f' ∘ g ∘ h ≃ f'` relative to `A`.
  have hhf : h.toFun.HomotopicRel f' A := by
    have h₁ := (HomotopicRel.precomp hfg h.toFun).mono fun x hx =>
      Set.mem_preimage.2 <| (he ⟨x, hx⟩).symm ▸ (e ⟨x, hx⟩).2
    have h₂ := HomotopicRel.comp_continuousMap hgf f'
    rw [ContinuousMap.id_comp] at h₁
    rw [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc] at h₂
    exact h₁.symm.trans h₂
  -- Hence `h ∘ g ≃ f' ∘ g ≃ id` relative to `B`.
  refine ⟨g, hgB, hgf, ((HomotopicRel.precomp hhf g).mono fun y hy => ?_).trans hfg⟩
  rw [Set.mem_preimage, hgB ⟨y, hy⟩]
  exact (e.symm ⟨y, hy⟩).2

/-- **Based homotopy inverses.** Let `x₀ ∈ X` and `y₀ ∈ Y` be points whose inclusions have the
homotopy extension property. A homotopy equivalence `h : X ≃ₕ Y` with `h x₀ = y₀` has a homotopy
inverse `g` with `g y₀ = x₀`, such that `g ∘ h` is homotopic to the identity relative to `x₀` and
`h ∘ g` is homotopic to the identity relative to `y₀`. -/
theorem HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel {x₀ : X} {y₀ : Y}
    (hx₀ : HasHomotopyExtensionProperty ({x₀} : Set X))
    (hy₀ : HasHomotopyExtensionProperty ({y₀} : Set Y)) (h : X ≃ₕ Y) (hh : h x₀ = y₀) :
    ∃ g : C(Y, X), g y₀ = x₀ ∧
      (g.comp h.toFun).HomotopicRel (ContinuousMap.id X) {x₀} ∧
      (h.toFun.comp g).HomotopicRel (ContinuousMap.id Y) {y₀} := by
  obtain ⟨g, hg, hgh, hhg⟩ := hx₀.exists_inverse_homotopicRel hy₀ h
    (Homeomorph.homeomorphOfUnique _ _)
    fun a => by rw [Set.mem_singleton_iff.1 a.2, hh, Set.mem_singleton_iff.1 (Subtype.prop _)]
  exact ⟨g, (hg ⟨y₀, rfl⟩).trans (Set.mem_singleton_iff.1 (Subtype.prop _)), hgh, hhg⟩

end TauCeti
