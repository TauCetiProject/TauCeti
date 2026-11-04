/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# The homotopy lifting property

A map `p : E → B` has the *homotopy lifting property* with respect to a space `A` when every
homotopy `H : I × A → B` whose initial map lifts along `p` to `f : A → E` lifts along `p` to a
homotopy `G : I × A → E` starting at `f`.  The property is stated for maps between topological
spaces in arbitrary universes.  Covering maps have it for every space
(`IsCoveringMap.hasHomotopyLiftingProperty`), as do product projections
(`TauCeti.hasHomotopyLiftingProperty_fst`) and homeomorphisms
(`Homeomorph.hasHomotopyLiftingProperty`); it is closed under composition
(`TauCeti.HasHomotopyLiftingProperty.comp`) and base change
(`TauCeti.HasHomotopyLiftingProperty.pullback`), and homotopy lifting of `U.restrictPreimage p`
lifts homotopies valued in `U` (`TauCeti.HasHomotopyLiftingProperty.exists_lift_of_mem`); it
depends on the space only up to homeomorphism (`Homeomorph.hasHomotopyLiftingProperty_iff`),
passes from open subsets along open embeddings
(`TauCeti.HasHomotopyLiftingProperty.of_isOpenEmbedding`), and a map with it lifts paths
(`TauCeti.HasHomotopyLiftingProperty.exists_path_lift`).

Serre fibrations, the maps with the homotopy lifting property with respect to every disk, are in
`TauCeti.Topology.Homotopy.SerreFibration.Basic`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the homotopy lifting property.
-/

public section

open unitInterval

universe u v w w'

section HomotopyLifting

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {A : Type w} [TopologicalSpace A] {A' : Type w'} [TopologicalSpace A'] {p : E → B}

namespace TauCeti

/-- A map `p : E → B` has the *homotopy lifting property* with respect to a space `A` when every
homotopy `H : I × A → B` whose initial map lifts along `p` to some `f : A → E` lifts along `p` to a
homotopy `G : I × A → E` starting at `f`. -/
@[expose] def HasHomotopyLiftingProperty (p : E → B) (A : Type w) [TopologicalSpace A] : Prop :=
  ∀ (f : C(A, E)) (H : C(I × A, B)), (∀ a, H (0, a) = p (f a)) →
    ∃ G : C(I × A, E), p ∘ G = H ∧ ∀ a, G (0, a) = f a

/-- A map with the homotopy lifting property with respect to a nonempty space lifts paths: a path
in `B` starting at `p e` lifts to a path in `E` starting at `e`. -/
theorem HasHomotopyLiftingProperty.exists_path_lift [Nonempty A]
    (h : HasHomotopyLiftingProperty p A) {e : E} {b : B} (γ : Path (p e) b) :
    ∃ Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  obtain ⟨G, hG, hG₀⟩ := h (.const A e) ⟨fun x ↦ γ x.1, by fun_prop⟩ fun _ ↦ γ.source
  let a : A := Classical.arbitrary A
  refine ⟨⟨fun t ↦ G (t, a), by fun_prop⟩, hG₀ a, funext fun t ↦ ?_⟩
  exact congrFun hG (t, a)

/-- A map with the homotopy lifting property with respect to a nonempty space, from a nonempty
space onto a path-connected space, is surjective. -/
theorem HasHomotopyLiftingProperty.surjective [Nonempty A] [Nonempty E] [PathConnectedSpace B]
    (h : HasHomotopyLiftingProperty p A) : Function.Surjective p := by
  intro b
  let e : E := Classical.arbitrary E
  obtain ⟨Γ, -, hΓ⟩ := h.exists_path_lift (PathConnectedSpace.somePath (p e) b)
  exact ⟨Γ 1, (congrFun hΓ 1).trans (Path.target _)⟩

/-- The projection `B × F → B` has the homotopy lifting property with respect to every space: a
homotopy lifts by keeping the `F`-coordinate of the initial lift fixed. -/
theorem hasHomotopyLiftingProperty_fst (F : Type*) [TopologicalSpace F] (A : Type w)
    [TopologicalSpace A] : HasHomotopyLiftingProperty (Prod.fst : B × F → B) A :=
  fun f H hH ↦ ⟨⟨fun x ↦ (H x, (f x.2).2), by fun_prop⟩, rfl, fun a ↦ Prod.ext (hH a) rfl⟩

/-- A homeomorphism has the homotopy lifting property with respect to every space. -/
theorem _root_.Homeomorph.hasHomotopyLiftingProperty (e : E ≃ₜ B) (A : Type w)
    [TopologicalSpace A] : HasHomotopyLiftingProperty e A :=
  fun f H hH ↦ ⟨(e.symm : C(B, E)).comp H, funext fun x ↦ by simp, fun a ↦ by simp [hH a]⟩

/-- The homotopy lifting property is closed under composition. -/
theorem HasHomotopyLiftingProperty.comp {C : Type*} [TopologicalSpace C] {q : B → C}
    (hq : HasHomotopyLiftingProperty q A) (hp : HasHomotopyLiftingProperty p A)
    (hpc : Continuous p) : HasHomotopyLiftingProperty (q ∘ p) A := by
  intro f H hH
  obtain ⟨G₁, hG₁, hG₁₀⟩ := hq ((ContinuousMap.mk p hpc).comp f) H hH
  obtain ⟨G₂, hG₂, hG₂₀⟩ := hp f G₁ hG₁₀
  exact ⟨G₂, by rw [Function.comp_assoc, hG₂, hG₁], hG₂₀⟩

/-- The homotopy lifting property passes to the base change `{(b', e) | g b' = p e} → B'` along
any continuous map `g : B' → B`. -/
theorem HasHomotopyLiftingProperty.pullback {B' : Type*} [TopologicalSpace B']
    (hp : HasHomotopyLiftingProperty p A) (g : C(B', B)) :
    HasHomotopyLiftingProperty (fun x : {x : B' × E // g x.1 = p x.2} ↦ x.1.1) A := by
  intro f H hH
  let f' : C(A, E) := ⟨fun a ↦ (f a).1.2, by fun_prop⟩
  obtain ⟨G, hG, hG₀⟩ := hp f' (g.comp H) fun a ↦ by
    simp only [ContinuousMap.comp_apply, hH a, f', ContinuousMap.coe_mk]
    exact (f a).2
  refine ⟨⟨fun x ↦ ⟨(H x, G x), (congrFun hG x).symm⟩, by fun_prop⟩, funext fun x ↦ rfl, fun a ↦ ?_⟩
  exact Subtype.ext (Prod.ext (hH a) (hG₀ a))

/-- If the restriction `U.restrictPreimage p : p ⁻¹' U → U` over `U : Set B` has the homotopy
lifting property with respect to `A`, then every homotopy `H : C(I × A, B)` valued in `U` whose
initial map lifts along `p` to `f : C(A, E)` lifts along `p` to a homotopy `G : C(I × A, E)`
starting at `f`. -/
theorem HasHomotopyLiftingProperty.exists_lift_of_mem {U : Set B}
    (h : HasHomotopyLiftingProperty (U.restrictPreimage p) A)
    (f : C(A, E)) (H : C(I × A, B)) (hHU : ∀ z, H z ∈ U) (hH : ∀ a, H (0, a) = p (f a)) :
    ∃ G : C(I × A, E), p ∘ G = H ∧ ∀ a, G (0, a) = f a := by
  have hfU (a : A) : f a ∈ p ⁻¹' U := by
    rw [Set.mem_preimage, ← hH a]
    exact hHU (0, a)
  obtain ⟨G, hG, hG₀⟩ := h ⟨fun a ↦ ⟨f a, hfU a⟩, by fun_prop⟩
    ⟨fun z ↦ ⟨H z, hHU z⟩, by fun_prop⟩ fun a ↦ Subtype.ext (hH a)
  exact ⟨(ContinuousMap.subtypeVal _).comp G,
    funext fun z ↦ congrArg Subtype.val (congrFun hG z),
    fun a ↦ congrArg Subtype.val (hG₀ a)⟩

/-- The homotopy lifting property with respect to a space passes to every space homeomorphic to
it. -/
theorem HasHomotopyLiftingProperty.of_homeomorph (h : HasHomotopyLiftingProperty p A')
    (e : A ≃ₜ A') : HasHomotopyLiftingProperty p A := by
  -- transport the lifting problem along `e` and its solution back along `e.symm`
  intro f H hH
  let φ : C(I × A, I × A') := ⟨fun x ↦ (x.1, e x.2), by fun_prop⟩
  let ψ : C(I × A', I × A) := ⟨fun x ↦ (x.1, e.symm x.2), by fun_prop⟩
  obtain ⟨G, hG, hG₀⟩ := h (f.comp e.symm) (H.comp ψ) fun y ↦ hH (e.symm y)
  refine ⟨G.comp φ, funext fun x ↦ ?_, fun x ↦ by simpa [φ] using hG₀ (e x)⟩
  simpa [φ, ψ] using congrFun hG (φ x)

/-- If `p` has the homotopy lifting property with respect to every open subset of `A'`, then it has
the homotopy lifting property with respect to every space admitting an open embedding into `A'`. -/
theorem HasHomotopyLiftingProperty.of_isOpenEmbedding
    (h : ∀ W : Set A', IsOpen W → HasHomotopyLiftingProperty p W)
    {e : A → A'} (he : Topology.IsOpenEmbedding e) :
    HasHomotopyLiftingProperty p A :=
  (h (Set.range e) he.isOpen_range).of_homeomorph he.toHomeomorph

end TauCeti

open TauCeti

/-- The homotopy lifting property with respect to a space depends on the space only up to
homeomorphism. -/
theorem Homeomorph.hasHomotopyLiftingProperty_iff (e : A ≃ₜ A') :
    HasHomotopyLiftingProperty p A ↔ HasHomotopyLiftingProperty p A' :=
  ⟨fun h ↦ h.of_homeomorph e.symm, fun h ↦ h.of_homeomorph e⟩

/-- A covering map has the homotopy lifting property with respect to every space. -/
theorem IsCoveringMap.hasHomotopyLiftingProperty (hp : IsCoveringMap p) (A : Type w)
    [TopologicalSpace A] : HasHomotopyLiftingProperty p A :=
  fun f H hH ↦ ⟨hp.liftHomotopy H f hH, hp.liftHomotopy_lifts H f hH, hp.liftHomotopy_zero H f hH⟩

