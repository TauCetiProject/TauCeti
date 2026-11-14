/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.Lifting.Basic
public import TauCeti.Topology.PathComponent

/-!
# The action of the fundamental group on the path components of a fibre

Let `p : E → B` be a map with the homotopy lifting property with respect to the unit
interval, for instance a Serre fibration
(`TauCeti.TopCat.hasHomotopyLiftingProperty_unitInterval_of_mem_serreFibrations`) or a Hurewicz
fibration (`TauCeti.IsHurewiczFibration.hasHomotopyLiftingProperty`). A path `γ` from `b₀` to
`b₁` in `B` lifts, from each point `x` of the fibre over `b₀`, to a path of `E` ending in the fibre
over `b₁`. The lift is not unique, but the path component of
its end in the fibre depends only on the path component of `x` in the fibre over `b₀` and on the
homotopy class of `γ` relative to its endpoints. This gives the **transport** of path components
of fibres (`TauCeti.HasHomotopyLiftingProperty.fiberComponentTransport`)

`π₀(p⁻¹(b₀)) → π₀(p⁻¹(b₁))`,

which is functorial in the path class, hence a bijection
(`TauCeti.HasHomotopyLiftingProperty.fiberComponentTransportEquiv`). For loops at `b` it is an
action of `π₁(B, b)` on `π₀(p⁻¹(b))`
(`TauCeti.HasHomotopyLiftingProperty.fiberComponentMulAction`). This action is the part of the
long exact homotopy sequence of a fibration at its low end that pointed-set exactness forgets.
When `p` is moreover continuous:

* two points of the fibre lie in the same path component of `E` exactly when their components
  lie in the same orbit (`TauCeti.HasHomotopyLiftingProperty.joined_iff_mem_orbit`);
* the stabilizer of the component of a point `e` of the fibre is the image of `π₁(E, e)` in
  `π₁(B, b)` (`TauCeti.HasHomotopyLiftingProperty.stabilizer_mk_eq_range`);
* when `B` is path connected, the path components of `E` are the orbits,
  `π₀(E) ≃ π₀(p⁻¹(b)) / π₁(B, b)`
  (`TauCeti.HasHomotopyLiftingProperty.orbitRelQuotientEquivZerothHomotopy`).

The analogous action of `π₁(B, b)` on the points of a fibre of a covering map is Mathlib's
monodromy action `IsCoveringMap.fundamentalGroupMulAction`, whose stabilizers are described in
`TauCeti.Topology.Homotopy.Monodromy.Basic`.

## Lifting null-homotopic loops

Everything rests on one consequence of homotopy lifting with respect to the interval
(`TauCeti.HasHomotopyLiftingProperty.joined_of_homotopic_refl`): a path of `E` between two
points of the fibre over `b` that lies over a loop at `b` homotopic to the constant loop can be
pushed into the fibre. Lifting the null-homotopy, starting from the path, gives a square in `E`
whose other three sides lie in the fibre. Two lifts of homotopic paths with starting points in one
component of the fibre are compared by applying this to the lift of one, run backwards, followed
by a path in the fibre and the lift of the other
(`TauCeti.HasHomotopyLiftingProperty.joined_of_homotopic`).

## Conventions

As for Mathlib's monodromy action, transport along `γ` followed by transport along `δ` is
transport along `γ.trans δ`, and multiplication in `FundamentalGroup B b` is
`FundamentalGroup.mul_def : g * h = h.trans g`, so the action is a left action.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2 (Theorem 4.41,
  the long exact sequence of a fibration) and Section 4.3 (Proposition 4.61).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti.HasHomotopyLiftingProperty

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b b₀ b₁ b₂ : B}

omit [TopologicalSpace B] in
/-- A map of the interval into `E` lying over `b` joins its end points within the fibre over
`b`. -/
private theorem joined_of_forall {u v : p ⁻¹' {b}} (c : C(I, E)) (hc : ∀ t, p (c t) = b)
    (h₀ : c 0 = u) (h₁ : c 1 = v) : Joined u v :=
  ⟨{ toFun t := ⟨c t, hc t⟩
     continuous_toFun := c.continuous.subtype_mk _
     source' := Subtype.ext h₀
     target' := Subtype.ext h₁ }⟩

/-- **A path over a null-homotopic loop joins points of one fibre component.** If `p` has the
homotopy lifting property with respect to the interval, and a path of `E` between two points of
the fibre over `b` lies over a loop at `b` homotopic to the constant loop, then the two points are
joined by a path in the fibre. -/
theorem joined_of_homotopic_refl (hp : HasHomotopyLiftingProperty p I) {γ : Path b b}
    (hγ : γ.Homotopic (Path.refl b)) {u v : p ⁻¹' {b}} (Γ : Path (u : E) v)
    (hΓ : ∀ t, p (Γ t) = γ t) : Joined u v := by
  obtain ⟨F⟩ := hγ
  -- Lift the null-homotopy `F` of `γ`, starting from `Γ`; the three other sides of the lifted
  -- square lie over `b`.
  obtain ⟨G, hG, hG₀⟩ := hp Γ.toContinuousMap ⟨fun x ↦ F x, F.continuous⟩
    fun t ↦ (F.apply_zero t).trans (hΓ t).symm
  have hGF (x : I × I) : p (G x) = F x := congrFun hG x
  have hbot (s : I) : p (G (s, 0)) = b := (hGF _).trans (F.source s)
  have htop (s : I) : p (G (s, 1)) = b := (hGF _).trans (F.target s)
  have hend (t : I) : p (G (1, t)) = b := (hGF _).trans (F.apply_one t)
  refine ((joined_of_forall (v := ⟨G (1, 0), hbot 1⟩) (G.comp ⟨fun s ↦ (s, 0), by fun_prop⟩)
    hbot ((hG₀ 0).trans Γ.source) rfl).trans
    (joined_of_forall (v := ⟨G (1, 1), htop 1⟩) (G.comp ⟨fun t ↦ (1, t), by fun_prop⟩)
      hend rfl rfl)).trans
    (joined_of_forall (G.comp ⟨fun s ↦ (s, 1), by fun_prop⟩) htop ((hG₀ 1).trans Γ.target)
      rfl).symm

/-- **Lifts of homotopic paths end in one fibre component.** Let `Γ` and `Γ'` be paths of `E`
lying over paths `γ` and `γ'` of `B` from `b₀` to `b₁` which are homotopic relative to their
endpoints. If the starting points of `Γ` and `Γ'` are joined in the fibre over `b₀`, then their
end points are joined in the fibre over `b₁`. -/
theorem joined_of_homotopic (hp : HasHomotopyLiftingProperty p I) {γ γ' : Path b₀ b₁}
    (h : γ.Homotopic γ') {x x' : p ⁻¹' {b₀}} {y y' : p ⁻¹' {b₁}} (Γ : Path (x : E) y)
    (Γ' : Path (x' : E) y') (hΓ : ∀ t, p (Γ t) = γ t) (hΓ' : ∀ t, p (Γ' t) = γ' t)
    (hx : Joined x x') : Joined y y' := by
  -- The path `Γ⁻¹ * c * Γ'`, for a path `c` in the fibre, lies over the null-homotopic loop
  -- `γ⁻¹ * 1 * γ'`.
  let c : Path (x : E) x' := hx.somePath.map continuous_subtype_val
  have hc (t : I) : p (c t) = b₀ := (hx.somePath t).2
  refine hp.joined_of_homotopic_refl (γ := (γ.symm.trans (Path.refl b₀)).trans γ') ?_
    ((Γ.symm.trans c).trans Γ') fun t ↦ ?_
  · exact ((Path.Homotopic.trans_refl γ.symm).hcomp h.symm).trans
      (Path.Homotopic.symm_trans γ)
  · simp only [Path.trans_apply, Path.symm_apply, Path.refl_apply]
    split_ifs <;> simp [hΓ, hΓ', hc]

/-- **Transport of the path components of the fibres** of a map with the homotopy lifting
property with respect to the interval, along a homotopy class `γ` of paths from `b₀` to `b₁`:
the path component of a point `x` of the fibre over `b₀` goes to the path component of the end
of any lift of a representative of `γ` starting at `x`
(`TauCeti.HasHomotopyLiftingProperty.fiberComponentTransport_mk`). -/
def fiberComponentTransport (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) :
    ZerothHomotopy (p ⁻¹' {b₀}) → ZerothHomotopy (p ⁻¹' {b₁}) :=
  fun a ↦ Quotient.lift₂ (s₁ := Path.Homotopic.setoid b₀ b₁) (s₂ := pathSetoid _)
    (fun γ x ↦ ZerothHomotopy.mk (hp.exists_path_lift_fiber γ x).choose)
    (fun γ x γ' x' hγ hx ↦ ZerothHomotopy.mk_eq_mk_iff.2 <|
      hp.joined_of_homotopic hγ (hp.exists_path_lift_fiber γ x).choose_spec.choose
        (hp.exists_path_lift_fiber γ' x').choose_spec.choose
        (hp.exists_path_lift_fiber γ x).choose_spec.choose_spec
        (hp.exists_path_lift_fiber γ' x').choose_spec.choose_spec hx)
    γ a

/-- Transport of path components along the class of a path `γ` sends the component of `x` to
the component of the end `y` of any path of `E` from `x` lying over `γ`. -/
theorem fiberComponentTransport_mk (hp : HasHomotopyLiftingProperty p I) {γ : Path b₀ b₁}
    {x : p ⁻¹' {b₀}} {y : p ⁻¹' {b₁}} (Γ : Path (x : E) y) (hΓ : ∀ t, p (Γ t) = γ t) :
    hp.fiberComponentTransport (.mk γ) (.mk x) = .mk y :=
  ZerothHomotopy.mk_eq_mk_iff.2 <| hp.joined_of_homotopic (Path.Homotopic.refl γ)
    (hp.exists_path_lift_fiber γ x).choose_spec.choose Γ
    (hp.exists_path_lift_fiber γ x).choose_spec.choose_spec hΓ
    (Joined.refl x)

/-- Transport along the constant path is the identity. -/
@[simp]
theorem fiberComponentTransport_refl (hp : HasHomotopyLiftingProperty p I) (b : B) :
    hp.fiberComponentTransport (.refl b) = id := by
  funext a
  induction a with
  | mk x => exact hp.fiberComponentTransport_mk (Path.refl (x : E)) fun _ ↦ x.2

/-- Transport along a concatenation is the composite of the transports. -/
theorem fiberComponentTransport_trans (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) (δ : Path.Homotopic.Quotient b₁ b₂) :
    hp.fiberComponentTransport (γ.trans δ) =
      hp.fiberComponentTransport δ ∘ hp.fiberComponentTransport γ := by
  funext a
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  induction δ using Path.Homotopic.Quotient.ind with | mk δ =>
  induction a with | mk x =>
  obtain ⟨y, Γ, hΓ⟩ := hp.exists_path_lift_fiber γ x
  obtain ⟨z, Δ, hΔ⟩ := hp.exists_path_lift_fiber δ y
  rw [Function.comp_apply, hp.fiberComponentTransport_mk Γ hΓ,
    hp.fiberComponentTransport_mk Δ hΔ, ← Path.Homotopic.Quotient.mk_trans]
  refine hp.fiberComponentTransport_mk (Γ.trans Δ) fun t ↦ ?_
  simp only [Path.trans_apply]
  split_ifs <;> simp [hΓ, hΔ]

/-- Transport along a concatenation, applied to a path component. -/
@[simp]
theorem fiberComponentTransport_trans_apply (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) (δ : Path.Homotopic.Quotient b₁ b₂)
    (a : ZerothHomotopy (p ⁻¹' {b₀})) :
    hp.fiberComponentTransport (γ.trans δ) a =
      hp.fiberComponentTransport δ (hp.fiberComponentTransport γ a) :=
  congrFun (hp.fiberComponentTransport_trans γ δ) a

/-- Transport of path components of the fibres along a homotopy class of paths, as a bijection,
with inverse the transport along the reversed class. -/
def fiberComponentTransportEquiv (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) :
    ZerothHomotopy (p ⁻¹' {b₀}) ≃ ZerothHomotopy (p ⁻¹' {b₁}) where
  toFun := hp.fiberComponentTransport γ
  invFun := hp.fiberComponentTransport γ.symm
  left_inv a := by
    rw [← fiberComponentTransport_trans_apply, Path.Homotopic.Quotient.trans_symm,
      fiberComponentTransport_refl, id]
  right_inv a := by
    rw [← fiberComponentTransport_trans_apply, Path.Homotopic.Quotient.symm_trans,
      fiberComponentTransport_refl, id]

@[simp]
theorem fiberComponentTransportEquiv_apply (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) (a : ZerothHomotopy (p ⁻¹' {b₀})) :
    hp.fiberComponentTransportEquiv γ a = hp.fiberComponentTransport γ a :=
  (rfl)

@[simp]
theorem fiberComponentTransportEquiv_symm_apply (hp : HasHomotopyLiftingProperty p I)
    (γ : Path.Homotopic.Quotient b₀ b₁) (a : ZerothHomotopy (p ⁻¹' {b₁})) :
    (hp.fiberComponentTransportEquiv γ).symm a = hp.fiberComponentTransport γ.symm a :=
  (rfl)

/-- **The action of `π₁(B, b)` on the path components of the fibre over `b`**, by transport
along loops, for a map with the homotopy lifting property with respect to the interval. It is not
an instance, since it depends on the lifting property `hp`. -/
@[reducible]
def fiberComponentMulAction (hp : HasHomotopyLiftingProperty p I) (b : B) :
    MulAction (FundamentalGroup B b) (ZerothHomotopy (p ⁻¹' {b})) where
  smul g := hp.fiberComponentTransport g.toPath
  one_smul := congrFun (hp.fiberComponentTransport_refl b)
  mul_smul g h := hp.fiberComponentTransport_trans_apply h.toPath g.toPath

/-- An element of `π₁(B, b)` acts on the path components of the fibre by transport along the
loop class it represents. -/
theorem smul_eq_fiberComponentTransport (hp : HasHomotopyLiftingProperty p I)
    (g : FundamentalGroup B b) (a : ZerothHomotopy (p ⁻¹' {b})) :
    letI := hp.fiberComponentMulAction b
    g • a = hp.fiberComponentTransport g.toPath a :=
  (rfl)

/-- The class of a loop `γ` at `b` sends the path component of `x` to the path component of the
end `y` of any path of `E` from `x` lying over `γ`. -/
theorem fromPath_mk_smul_mk (hp : HasHomotopyLiftingProperty p I) {γ : Path b b}
    {x y : p ⁻¹' {b}} (Γ : Path (x : E) y) (hΓ : ∀ t, p (Γ t) = γ t) :
    letI := hp.fiberComponentMulAction b
    FundamentalGroup.fromPath (.mk γ) • ZerothHomotopy.mk x = ZerothHomotopy.mk y :=
  hp.fiberComponentTransport_mk Γ hΓ

/-- **Points of the fibre are joined in the total space iff their components lie in one orbit.**
For continuous `p`, two points of the fibre over `b` are joined by a path in `E` exactly when the
path components of the fibre containing them lie in one orbit of `π₁(B, b)`. -/
theorem joined_iff_mem_orbit (hp : HasHomotopyLiftingProperty p I) (hpc : Continuous p)
    {x y : p ⁻¹' {b}} :
    letI := hp.fiberComponentMulAction b
    Joined (x : E) y ↔
      ZerothHomotopy.mk y ∈ MulAction.orbit (FundamentalGroup B b) (ZerothHomotopy.mk x) := by
  let := hp.fiberComponentMulAction b
  rw [MulAction.mem_orbit_iff]
  constructor
  · -- A path of `E` from `x` to `y` lies over its image, a loop at `b`.
    rintro ⟨β⟩
    exact ⟨_, hp.fromPath_mk_smul_mk (γ := (β.map hpc).cast x.2.symm y.2.symm) β
      fun _ ↦ rfl⟩
  · -- A lift from `x` of a loop sending the component of `x` to that of `y` ends in the
    -- component of `y` in the fibre.
    rintro ⟨g, hg⟩
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective g.toPath
    obtain ⟨z, Γ, hΓ⟩ := hp.exists_path_lift_fiber γ x
    have hz : Joined z y := by
      rw [← ZerothHomotopy.mk_eq_mk_iff, ← hg, smul_eq_fiberComponentTransport, ← hγ]
      exact (hp.fiberComponentTransport_mk Γ hΓ).symm
    exact ⟨Γ.trans (hz.somePath.map continuous_subtype_val)⟩

/-- **Stabilizers are images of fundamental groups of the total space.** The stabilizer of the
path component of a point `e` of the fibre over `b` of a continuous map `p` is the image of
`π₁(E, e)` in `π₁(B, b)`. -/
theorem stabilizer_mk_eq_range (hp : HasHomotopyLiftingProperty p I) (hpc : Continuous p)
    (e : p ⁻¹' {b}) :
    letI := hp.fiberComponentMulAction b
    MulAction.stabilizer (FundamentalGroup B b) (ZerothHomotopy.mk e) =
      (FundamentalGroup.mapOfEq ⟨p, hpc⟩ (Set.eq_of_mem_singleton e.2)).range := by
  let := hp.fiberComponentMulAction b
  ext g
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective g.toPath
  obtain rfl : g = .fromPath (.mk γ) := by rw [hγ]
  rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  constructor
  · -- Close the lift of `γ` from `e` by a path in the fibre back to `e`: the resulting loop at
    -- `e` lies over `γ` followed by the constant loop.
    intro hg
    obtain ⟨z, Γ, hΓ⟩ := hp.exists_path_lift_fiber γ e
    have hz : Joined z e := by
      rw [← ZerothHomotopy.mk_eq_mk_iff, ← hp.fromPath_mk_smul_mk Γ hΓ, hg]
    refine ⟨.fromPath (.mk (Γ.trans (hz.somePath.map continuous_subtype_val))), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]
    refine congrArg _ ?_
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.eq]
    convert Path.Homotopic.trans_refl γ using 1
    ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply]
    split_ifs
    · exact hΓ _
    · exact (hz.somePath _).2
  · -- A loop at `e` is a lift of its image from `e`.
    rintro ⟨δ, hδ⟩
    obtain ⟨β, hβ⟩ := Path.Homotopic.Quotient.mk_surjective δ.toPath
    obtain rfl : δ = .fromPath (.mk β) := by rw [hβ]
    rw [← hδ, FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast]
    exact hp.fromPath_mk_smul_mk β fun _ ↦ rfl

/-- **The path components of the total space are the orbits of `π₁(B, b)`** on the path
components of the fibre over `b`, when `p` is continuous and `B` is path connected: the inclusion
of the fibre induces a bijection `π₀(p⁻¹(b)) / π₁(B, b) ≃ π₀(E)`. -/
def orbitRelQuotientEquivZerothHomotopy (hp : HasHomotopyLiftingProperty p I)
    (hpc : Continuous p) [PathConnectedSpace B] (b : B) :
    letI := hp.fiberComponentMulAction b
    MulAction.orbitRel.Quotient (FundamentalGroup B b) (ZerothHomotopy (p ⁻¹' {b})) ≃
      ZerothHomotopy E :=
  letI := hp.fiberComponentMulAction b
  Equiv.ofBijective
    (Quotient.lift
      (ZerothHomotopy.lift (fun x : p ⁻¹' {b} ↦ ZerothHomotopy.mk (x : E))
        fun _ _ γ ↦ ZerothHomotopy.sound (γ.map continuous_subtype_val))
      fun a a' h ↦ by
        induction a with | mk x =>
        induction a' with | mk y =>
        exact ZerothHomotopy.mk_eq_mk_iff.2
          ((hp.joined_iff_mem_orbit hpc).2 (MulAction.orbitRel_apply.1 h)).symm)
    ⟨fun q q' h ↦ by
      induction q using Quotient.ind with | _ a =>
      induction q' using Quotient.ind with | _ a' =>
      induction a with | mk x =>
      induction a' with | mk y =>
      exact Quotient.sound (MulAction.orbitRel_apply.2
        ((hp.joined_iff_mem_orbit hpc).1 (ZerothHomotopy.mk_eq_mk_iff.1 h).symm)),
    fun c ↦ by
      induction c with | mk y =>
      obtain ⟨x, hx⟩ := hp.exists_joined b y
      exact ⟨Quotient.mk _ (ZerothHomotopy.mk x), ZerothHomotopy.mk_eq_mk_iff.2 hx⟩⟩

@[simp]
theorem orbitRelQuotientEquivZerothHomotopy_mk (hp : HasHomotopyLiftingProperty p I)
    (hpc : Continuous p) [PathConnectedSpace B] (x : p ⁻¹' {b}) :
    letI := hp.fiberComponentMulAction b
    hp.orbitRelQuotientEquivZerothHomotopy hpc b
        (Quotient.mk (MulAction.orbitRel _ _) (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (x : E) :=
  (rfl)

end TauCeti.HasHomotopyLiftingProperty
