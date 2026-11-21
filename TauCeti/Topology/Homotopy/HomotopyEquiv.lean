/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Homotopy equivalences: path connectedness, products, and slices of a cylinder

A homotopy equivalence `e : X ≃ₕ Y` is not surjective, so path connectedness of `Y` cannot be
read off from the image of a path in `X`. What replaces surjectivity is the trace of the
homotopy `e.toFun ∘ e.invFun ≃ id`: evaluated at a point `y`, it is a path from
`e.toFun (e.invFun y)` to `y`. Two points of `Y` are therefore joined to points in the image of
`e.toFun`, which are joined to each other because `X` is path connected.

This is the prerequisite for the base-point-free homotopy-group statements in
`TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv`, which need the target space to be path
connected before base-point change is available there. The file also records that the product
`ContinuousMap.HomotopyEquiv.prodCongr` of two homotopy equivalences acts componentwise, and that
the projection `X × Y → X` is a homotopy equivalence when `Y` is contractible.

Finally, the file records that a cylinder `X × [a, b]` is homotopy equivalent to `X`
through any of its slices `X × {t}`: the interval deforms linearly onto the point `t`. This is how
the two ends of a cylinder are seen to induce isomorphisms on homology.
In the same way, a product `X × E` with a real vector space `E` deforms onto its zero section
`X × {0}` by scaling the second factor.

It also records that inverting a homotopy equivalence twice gives it back, and that a left and
a right homotopy inverse of the same map are homotopic, so that a left homotopy inverse of a
homotopy equivalence is automatically a right homotopy inverse.

## Main declarations

* `ContinuousMap.HomotopyEquiv.symm_symm`: the double inverse of a homotopy equivalence is itself.
* `ContinuousMap.HomotopyEquiv.nonempty` and `ContinuousMap.HomotopyEquiv.nonempty_iff`:
  nonemptiness is invariant under homotopy equivalence.
* `ContinuousMap.Homotopic.preconnectedSpace_of_comp_homotopic_id`,
  `ContinuousMap.Homotopic.connectedSpace_of_comp_homotopic_id`: (pre)connectedness passes to
  homotopy retracts.
* `ContinuousMap.HomotopyEquiv.preconnectedSpace`, `ContinuousMap.HomotopyEquiv.connectedSpace`:
  a space homotopy equivalent to a (pre)connected space is (pre)connected.
* `ContinuousMap.HomotopyEquiv.pathConnectedSpace`: a space homotopy equivalent to a path
  connected space is path connected.
* `ContinuousMap.HomotopyEquiv.zerothHomotopyCongr`: a homotopy equivalence induces a bijection
  of the sets of path components.
* `ContinuousMap.HomotopyEquiv.prodCongr_apply`: the product of two homotopy equivalences acts
  componentwise.
* `ContinuousMap.HomotopyEquiv.prodContractible`: the homotopy equivalence `X × Y ≃ₕ X` given by
  the projection, for `Y` contractible.
* `ContinuousMap.HomotopyEquiv.prodIcc`: the slice `x ↦ (x, t)` is a homotopy equivalence
  `X ≃ₕ X × [a, b]`, with homotopy inverse the projection.
* `ContinuousMap.HomotopyEquiv.prodZeroSection`: for a real vector space `E`, the zero section
  `x ↦ (x, 0)` is a homotopy equivalence `X ≃ₕ X × E`, with homotopy inverse the projection.
* `ContinuousMap.Homotopic.homotopic_of_comp_homotopic_id`: a left and a right homotopy inverse
  of the same map are homotopic.
* `ContinuousMap.Homotopic.comp_homotopic_id_of_comp_homotopic_id`: a left homotopy inverse that
  has a left homotopy inverse itself is a right homotopy inverse.
* `ContinuousMap.HomotopyEquiv.toFun_comp_homotopic_id_of_comp_toFun_homotopic_id`: a left
  homotopy inverse of a homotopy equivalence is a right homotopy inverse.
-/

public section

namespace ContinuousMap

open scoped ContinuousMap

variable {X Y Z Z' : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace Z']

/-- Inverting a homotopy equivalence twice gives it back. -/
@[simp]
theorem HomotopyEquiv.symm_symm (e : X ≃ₕ Y) : e.symm.symm = e :=
  rfl

/-- A space homotopy equivalent to a nonempty space is nonempty. -/
theorem HomotopyEquiv.nonempty [Nonempty X] (e : X ≃ₕ Y) : Nonempty Y :=
  ‹Nonempty X›.map e

/-- Homotopy equivalent spaces are simultaneously nonempty. -/
theorem HomotopyEquiv.nonempty_iff (e : X ≃ₕ Y) : Nonempty X ↔ Nonempty Y :=
  ⟨fun _ ↦ e.nonempty, fun _ ↦ e.symm.nonempty⟩

/-- **Preconnectedness passes to homotopy retracts.** If `g ∘ f ≃ id_X` for continuous maps
`f : C(X, Y)` and `g : C(Y, X)` and `Y` is preconnected, then `X` is preconnected. -/
theorem Homotopic.preconnectedSpace_of_comp_homotopic_id [PreconnectedSpace Y]
    {f : C(X, Y)} {g : C(Y, X)} (h : (g.comp f).Homotopic (ContinuousMap.id X)) :
    PreconnectedSpace X := by
  obtain ⟨H⟩ := h
  refine preconnectedSpace_iff_clopen.2 fun s hs ↦ ?_
  -- Every point `x` is joined to `g (f x)` by the path `t ↦ H (t, x)`, so they agree on clopen
  -- sets.
  have hmem (x : X) : x ∈ s ↔ f x ∈ g ⁻¹' s := by
    let γ := H.evalAt x
    have h0eq : γ 0 = g (f x) := γ.source
    have h1eq : γ 1 = x := γ.target
    rcases isClopen_iff.1 (hs.preimage γ.continuous) with h0 | h1
    · constructor <;> intro hx
      · exact False.elim
          (Set.eq_empty_iff_forall_notMem.1 h0 1 (by rw [Set.mem_preimage, h1eq]; exact hx))
      · exact False.elim
          (Set.eq_empty_iff_forall_notMem.1 h0 0 (by rw [Set.mem_preimage, h0eq]; exact hx))
    · have h0' : (0 : unitInterval) ∈ γ ⁻¹' s := h1.symm ▸ trivial
      have h1' : (1 : unitInterval) ∈ γ ⁻¹' s := h1.symm ▸ trivial
      rw [Set.mem_preimage, h0eq] at h0'
      rw [Set.mem_preimage, h1eq] at h1'
      exact ⟨fun _ ↦ h0', fun _ ↦ h1'⟩
  rcases isClopen_iff.1 (hs.preimage g.continuous) with h_empty | h_univ
  · left; ext x; simp [hmem x, h_empty]
  · right; ext x; simp [hmem x, h_univ]

/-- **Connectedness passes to homotopy retracts.** If `g ∘ f ≃ id_X` for continuous maps
`f : C(X, Y)` and `g : C(Y, X)` and `Y` is connected, then `X` is connected. -/
theorem Homotopic.connectedSpace_of_comp_homotopic_id [ConnectedSpace Y]
    {f : C(X, Y)} {g : C(Y, X)} (h : (g.comp f).Homotopic (ContinuousMap.id X)) :
    ConnectedSpace X :=
  { toPreconnectedSpace := h.preconnectedSpace_of_comp_homotopic_id
    toNonempty := (inferInstance : Nonempty Y).map g }

/-- **Preconnectedness is a homotopy invariant.** A space homotopy equivalent to a preconnected
space is preconnected. -/
theorem HomotopyEquiv.preconnectedSpace [PreconnectedSpace X] (e : X ≃ₕ Y) :
    PreconnectedSpace Y :=
  e.right_inv.preconnectedSpace_of_comp_homotopic_id

/-- **Preconnectedness is preserved and reflected by homotopy equivalences.** -/
theorem HomotopyEquiv.preconnectedSpace_iff (e : X ≃ₕ Y) :
    PreconnectedSpace X ↔ PreconnectedSpace Y :=
  ⟨fun _ ↦ e.preconnectedSpace, fun _ ↦ e.symm.preconnectedSpace⟩

/-- **Connectedness is a homotopy invariant.** A space homotopy equivalent to a connected space
is connected. -/
theorem HomotopyEquiv.connectedSpace [ConnectedSpace X] (e : X ≃ₕ Y) : ConnectedSpace Y :=
  e.right_inv.connectedSpace_of_comp_homotopic_id

/-- **Connectedness is preserved and reflected by homotopy equivalences.** -/
theorem HomotopyEquiv.connectedSpace_iff (e : X ≃ₕ Y) : ConnectedSpace X ↔ ConnectedSpace Y :=
  ⟨fun _ ↦ e.connectedSpace, fun _ ↦ e.symm.connectedSpace⟩

/-- **Path connectedness is a homotopy invariant.** A space homotopy equivalent to a path
connected space is path connected. -/
theorem HomotopyEquiv.pathConnectedSpace [PathConnectedSpace X]
    (e : X ≃ₕ Y) : PathConnectedSpace Y where
  nonempty := (PathConnectedSpace.nonempty (X := X)).map e.toFun
  joined y₀ y₁ :=
    -- Evaluating the homotopy `e.toFun ∘ e.invFun ≃ id` at `y` is a path from
    -- `e.toFun (e.invFun y)` to `y`.
    have trace : ∀ y : Y, Joined (e.toFun (e.invFun y)) y := fun y => ⟨e.right_inv.some.evalAt y⟩
    ((trace y₀).symm.trans
        (Joined.map ⟨PathConnectedSpace.somePath (e.invFun y₀) (e.invFun y₁)⟩
          e.toFun.continuous)).trans
      (trace y₁)

/-- **The set of path components is a homotopy invariant.** A homotopy equivalence induces a
bijection of the sets of path components: the two composites are homotopic to the identity, so
they move each point within its path component. -/
def HomotopyEquiv.zerothHomotopyCongr (e : X ≃ₕ Y) : ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := Quotient.map e fun _ _ h ↦ h.map e.toFun.continuous
  invFun := Quotient.map e.symm fun _ _ h ↦ h.map e.invFun.continuous
  left_inv c := Quotient.inductionOn c fun a ↦ Quotient.sound ⟨e.left_inv.some.evalAt a⟩
  right_inv c := Quotient.inductionOn c fun b ↦ Quotient.sound ⟨e.right_inv.some.evalAt b⟩

@[simp]
theorem HomotopyEquiv.zerothHomotopyCongr_mk (e : X ≃ₕ Y) (a : X) :
    e.zerothHomotopyCongr (.mk a) = .mk (e a) :=
  (rfl)

@[simp]
theorem HomotopyEquiv.zerothHomotopyCongr_symm_mk (e : X ≃ₕ Y) (b : Y) :
    e.zerothHomotopyCongr.symm (.mk b) = .mk (e.symm b) :=
  (rfl)

/-- The product of two homotopy equivalences acts componentwise. -/
@[simp]
theorem HomotopyEquiv.prodCongr_apply (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z')
    (x : X × Z) : h₁.prodCongr h₂ x = (h₁ x.1, h₂ x.2) :=
  (rfl)

variable (X Y) in
/-- The projection `X × Y → X` is a homotopy equivalence when `Y` is contractible: its homotopy
inverse includes `X` at a point of `Y` to which `Y` contracts. -/
noncomputable def HomotopyEquiv.prodContractible [ContractibleSpace Y] :
    (X × Y) ≃ₕ X where
  toFun := fst
  invFun := (ContinuousMap.id X).prodMk (const X (id_nullhomotopic Y).choose)
  left_inv := by
    obtain ⟨H⟩ := (id_nullhomotopic Y).choose_spec
    exact Homotopic.symm ⟨{
      toFun q := (q.2.1, H (q.1, q.2.2))
      continuous_toFun := by fun_prop
      map_zero_left _ := by simp
      map_one_left _ := by simp }⟩
  right_inv := Homotopic.refl _

/-- The underlying map of the homotopy equivalence `X × Y ≃ₕ X` for contractible `Y` is the
projection. -/
theorem HomotopyEquiv.prodContractible_toFun [ContractibleSpace Y] :
    (HomotopyEquiv.prodContractible X Y).toFun = fst :=
  (rfl)

/-- The homotopy equivalence `X × Y ≃ₕ X` for contractible `Y` is the projection. -/
@[simp]
theorem HomotopyEquiv.coe_prodContractible [ContractibleSpace Y] :
    ⇑(HomotopyEquiv.prodContractible X Y) = Prod.fst :=
  (rfl)

/-- **A cylinder deforms onto each of its slices.** For a point `t` of the interval `[a, b]`, the
slice `x ↦ (x, t)` is a homotopy equivalence `X ≃ₕ X × [a, b]`, with homotopy inverse the
projection: at time `s` a point `(x, u)` is sent to `(x, t + s (u - t))`. -/
def HomotopyEquiv.prodIcc {a b : ℝ} (t : Set.Icc a b) :
    X ≃ₕ X × Set.Icc a b where
  toFun := ⟨fun x ↦ (x, t), by fun_prop⟩
  invFun := .fst
  left_inv := ⟨.refl _⟩
  right_inv := ⟨
    { toFun p := (p.2.1, ⟨t + p.1 * (p.2.2 - t), by
        obtain ⟨⟨s, hs₀, hs₁⟩, -, u, hu₀, hu₁⟩ := p
        obtain ⟨t, ht₀, ht₁⟩ := t
        constructor <;> nlinarith⟩)
      continuous_toFun := by fun_prop
      map_zero_left p := by simp
      map_one_left p := by simp }⟩

/-- The slice homotopy equivalence at `t` sends `x` to `(x, t)`. -/
@[simp]
theorem HomotopyEquiv.prodIcc_apply {a b : ℝ} (t : Set.Icc a b) (x : X) :
    HomotopyEquiv.prodIcc t x = (x, t) :=
  (rfl)

/-- The homotopy inverse of a slice homotopy equivalence is the projection. -/
@[simp]
theorem HomotopyEquiv.prodIcc_symm_apply {a b : ℝ} (t : Set.Icc a b)
    (p : X × Set.Icc a b) : (HomotopyEquiv.prodIcc t).symm p = p.1 :=
  (rfl)

section ZeroSection

variable (X) (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]

/-- **The zero section of a product with a real vector space is a homotopy equivalence.** The
zero section `x ↦ (x, 0)` is a homotopy equivalence `X ≃ₕ X × E`, with homotopy inverse the
projection: at time `t` a point `(x, v)` is sent to `(x, t • v)`. -/
def HomotopyEquiv.prodZeroSection : X ≃ₕ X × E where
  toFun := ⟨fun x ↦ (x, 0), by fun_prop⟩
  invFun := .fst
  left_inv := ⟨.refl _⟩
  right_inv := ⟨
    { toFun p := (p.2.1, (p.1 : ℝ) • p.2.2)
      continuous_toFun := by fun_prop
      map_zero_left p := by simp
      map_one_left p := by simp }⟩

/-- The zero section homotopy equivalence sends `x` to `(x, 0)`. -/
@[simp]
theorem HomotopyEquiv.prodZeroSection_apply (x : X) :
    HomotopyEquiv.prodZeroSection X E x = (x, 0) :=
  (rfl)

/-- The homotopy inverse of the zero section homotopy equivalence is the projection. -/
@[simp]
theorem HomotopyEquiv.prodZeroSection_symm_apply (p : X × E) :
    (HomotopyEquiv.prodZeroSection X E).symm p = p.1 :=
  (rfl)

end ZeroSection

/-- **Left and right homotopy inverses are homotopic.** If `l ∘ f ≃ id` and `f ∘ r ≃ id`, then
`l ≃ l f r ≃ r`. In particular `f` is then a homotopy equivalence, with `l` and `r` both two-sided
homotopy inverses. -/
theorem Homotopic.homotopic_of_comp_homotopic_id {f : C(X, Y)}
    {l r : C(Y, X)} (hl : (l.comp f).Homotopic (ContinuousMap.id X))
    (hr : (f.comp r).Homotopic (ContinuousMap.id Y)) : l.Homotopic r := by
  have h₁ := (Homotopic.refl l).comp hr.symm
  have h₂ := hl.comp (Homotopic.refl r)
  simp only [comp_id, id_comp, comp_assoc] at h₁ h₂
  exact h₁.trans h₂

/-- **A left homotopy inverse with its own left homotopy inverse is a right homotopy inverse.** If
`l ∘ f ≃ id` and `k ∘ l ≃ id`, then `k ≃ f` as left and right homotopy inverses of `l`, so
`f ∘ l ≃ k ∘ l ≃ id`. -/
theorem _root_.ContinuousMap.Homotopic.comp_homotopic_id_of_comp_homotopic_id {f : C(X, Y)}
    {l : C(Y, X)} {k : C(X, Y)} (hl : (l.comp f).Homotopic (ContinuousMap.id X))
    (hk : (k.comp l).Homotopic (ContinuousMap.id Y)) :
    (f.comp l).Homotopic (ContinuousMap.id Y) :=
  ((hk.homotopic_of_comp_homotopic_id hl).symm.comp (.refl l)).trans hk

/-- **A left homotopy inverse of a homotopy equivalence is a right homotopy inverse.** If
`e : X ≃ₕ Y` and `g : Y → X` satisfy `g ∘ e ≃ id`, then also `e ∘ g ≃ id`, since `g` is
homotopic to the right homotopy inverse `e⁻¹`. -/
theorem HomotopyEquiv.toFun_comp_homotopic_id_of_comp_toFun_homotopic_id
    (e : X ≃ₕ Y) {g : C(Y, X)}
    (hg : (g.comp e.toFun).Homotopic (ContinuousMap.id X)) :
    (e.toFun.comp g).Homotopic (ContinuousMap.id Y) :=
  ((Homotopic.refl e.toFun).comp
    (hg.homotopic_of_comp_homotopic_id e.right_inv)).trans e.right_inv

end ContinuousMap
