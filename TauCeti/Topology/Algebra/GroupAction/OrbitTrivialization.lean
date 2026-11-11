/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Trivializations of orbit projections from equivariant maps

Let a topological group `G` act continuously on `X`, and let `π : X → X ⧸ G` be the projection
to the orbit space, with its quotient topology. Over an open set `W` of orbits, a continuous map
`u : π⁻¹ W → G` with `u (g • x) = g * u x` trivializes `π` as a principal `G`-bundle: the map
`x ↦ (π x, u x)` is a homeomorphism `π⁻¹ W ≃ W × G`. Its inverse sends `(π x, g)` to
`(g * (u x)⁻¹) • x`; the point `(u x)⁻¹ • x` depends only on the orbit of `x`, so it defines a
continuous local section of `π` over `W`, by the universal property of the quotient topology.

This is the standard passage from an equivariant map to a local product structure for free
actions; see for instance Husemoller, *Fibre Bundles*, Chapter 4. It turns the construction of
equivariant maps into the construction of principal-bundle charts, using Mathlib's
`Trivialization`.

Dually, for a single orbit: if `G` acts on `X` with continuous orbit map `g ↦ g • x₀`, a section
`s` of the orbit map, continuous on an open set `U`, trivializes the orbit map over `U` with fibre
the stabilizer of `x₀`, by `g ↦ (g • x₀, s (g • x₀)⁻¹ * g)` with inverse `(z, h) ↦ s z * h`. This
is `Subgroup.localSectionTrivializationOfCosetFibers` for the orbit map, whose fibres are the left
cosets of the stabilizer; see Steenrod, *The Topology of Fibre Bundles*, §7.

More generally, a continuous map `p : E → X` that is equivariant for actions of `G` is trivial over
`U`, with fibre `p⁻¹(x₀)`, by `e ↦ (p e, s (p e)⁻¹ • e)` with inverse `(z, y) ↦ s z • y`: the local
section translates the fibre over `x₀` onto the nearby fibres. This is how homogeneous bundles,
such as the maps between Stiefel manifolds that forget vectors of a frame, are shown to be locally
trivial.

## Main definitions and results

* `TauCeti.orbitTrivialization`: the trivialization of the orbit projection over `W` determined
  by a continuous equivariant map `u : π⁻¹ W → G`.
* `TauCeti.orbitTrivialization_apply` and `TauCeti.orbitTrivialization_symm_apply_mk`: the chart
  and its inverse.
* `TauCeti.orbitTrivialization_apply_smul`: the chart intertwines the action on `X` with left
  multiplication on the fibre `G`.
* `TauCeti.orbitMapTrivialization`: the trivialization of the orbit map `g ↦ g • x₀` over an open
  set, with fibre the stabilizer of `x₀`, determined by a continuous local section.
* `TauCeti.orbitMapTrivialization_apply_mul`: it intertwines right multiplication by the
  stabilizer on `G` with right multiplication on the fibre.
* `TauCeti.equivariantTrivialization`: the trivialization of an equivariant map over an open set,
  with fibre the fibre over `x₀`, determined by a continuous local section of the orbit map of `x₀`.
-/

public section

open Bundle MulAction Set Topology

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {W : Set (Quotient (orbitRel G X))} {u : X → G}

/-- The point `(u x)⁻¹ • x` only depends on the orbit of `x` when `u` is equivariant on a
saturated set containing `x`. -/
private theorem inv_smul_eq_of_smul_eq_mul
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x)
    {x y : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (hxy : Quotient.mk (orbitRel G X) y = Quotient.mk (orbitRel G X) x) :
    (u y)⁻¹ • y = (u x)⁻¹ • x := by
  obtain ⟨g, rfl⟩ : ∃ g : G, g • x = y := Quotient.exact hxy
  rw [hu_smul g x hx, mul_inv_rev, mul_smul, inv_smul_smul]

variable [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X] [ContinuousSMul G X]

/-- The trivialization of the orbit projection `X → X ⧸ G` over an open set `W` of orbits,
determined by a continuous map `u : X → G` that is equivariant on the preimage of `W`. It sends
`x` to `(π x, u x)`, and its inverse sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
noncomputable def orbitTrivialization (W : Set (Quotient (orbitRel G X))) (hW : IsOpen W)
    (u : X → G) (hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W))
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x) :
    Trivialization G (Quotient.mk (orbitRel G X)) where
  toFun x := (Quotient.mk _ x, u x)
  invFun p := p.2 • (u p.1.out)⁻¹ • p.1.out
  source := Quotient.mk (orbitRel G X) ⁻¹' W
  target := W ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' p hp := by simpa using hp.1
  left_inv' x hx := by
    simp only [inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _), smul_inv_smul]
  right_inv' p hp := by
    have hout : p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by simpa using hp.1
    have hsec : (u p.1.out)⁻¹ • p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by
      simpa using hp.1
    simp [hu_smul _ _ hsec, hu_smul _ _ hout]
  open_source := hW.preimage continuous_quot_mk
  open_target := hW.prod isOpen_univ
  continuousOn_toFun := continuous_quot_mk.continuousOn.prodMk hu
  continuousOn_invFun := by
    have hsec : ContinuousOn (fun y : Quotient (orbitRel G X) ↦ (u y.out)⁻¹ • y.out) W := by
      rw [isQuotientMap_quotient_mk'.continuousOn_isOpen_iff hW]
      refine ((hu.inv).smul continuousOn_id).congr fun x hx ↦ ?_
      exact inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _)
    exact continuousOn_snd.smul (hsec.comp continuousOn_fst fun _ hp ↦ hp.1)
  baseSet := W
  open_baseSet := hW
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hW : IsOpen W} {hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W)}
  {hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x}

/-- `orbitTrivialization` sends `x` to its orbit together with `u x`. -/
@[simp]
theorem orbitTrivialization_apply (x : X) :
    orbitTrivialization W hW u hu hu_smul x = (Quotient.mk (orbitRel G X) x, u x) :=
  (rfl)

/-- The base of `orbitTrivialization` is the given open set of orbits. -/
@[simp]
theorem orbitTrivialization_baseSet : (orbitTrivialization W hW u hu hu_smul).baseSet = W :=
  (rfl)

/-- The inverse of `orbitTrivialization` sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
@[simp]
theorem orbitTrivialization_symm_apply_mk {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (g : G) :
    (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.symm
      (Quotient.mk _ x, g) = (g * (u x)⁻¹) • x := by
  have hsrc : (g * (u x)⁻¹) • x ∈ (orbitTrivialization W hW u hu hu_smul).source := by
    simpa [Trivialization.mem_source] using hx
  have happly : orbitTrivialization W hW u hu hu_smul ((g * (u x)⁻¹) • x) =
      (Quotient.mk _ x, g) := by
    simp [hu_smul _ _ hx]
  rw [← happly]
  exact (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.left_inv hsrc

/-- `orbitTrivialization` intertwines the action of `G` on `X` with left multiplication on the
fibre `G`. -/
theorem orbitTrivialization_apply_smul (g : G) {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W) :
    orbitTrivialization W hW u hu hu_smul (g • x) =
      ((orbitTrivialization W hW u hu hu_smul x).1,
        g * (orbitTrivialization W hW u hu hu_smul x).2) := by
  simp only [orbitTrivialization_apply, hu_smul g x hx, orbitRel.Quotient.quotient_smul_eq]

end TauCeti

/-! ### Orbit maps with local sections -/

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] [TopologicalSpace X]

/-- Let `G` act on `X` with continuous orbit map `g ↦ g • x₀`. A section `s` of the orbit map,
continuous on an open set `U`, defines the local trivialization of the orbit map over `U` with
fibre the stabilizer of `x₀`: it sends `g` over `U` to `(g • x₀, s (g • x₀)⁻¹ * g)`, and its
inverse sends `(z, h)` to `s z * h`. -/
noncomputable def orbitMapTrivialization (x₀ : X) (hx₀ : Continuous fun g : G ↦ g • x₀)
    (U : Set X) (hU : IsOpen U) (s : X → G) (hs : ContinuousOn s U)
    (hsec : ∀ z ∈ U, s z • x₀ = z) :
    Trivialization (stabilizer G x₀) fun g : G ↦ g • x₀ :=
  (stabilizer G x₀).localSectionTrivializationOfCosetFibers hx₀
    (smul_eq_smul_iff_inv_mul_mem_stabilizer x₀) U hU s hs hsec

variable {x₀ : X} {hx₀ : Continuous fun g : G ↦ g • x₀} {U : Set X} {hU : IsOpen U} {s : X → G}
  {hs : ContinuousOn s U} {hsec : ∀ z ∈ U, s z • x₀ = z}

/-- The base of `orbitMapTrivialization` is the domain of the local section. -/
@[simp]
theorem orbitMapTrivialization_baseSet :
    (orbitMapTrivialization x₀ hx₀ U hU s hs hsec).baseSet = U :=
  Subgroup.localSectionTrivializationOfCosetFibers_baseSet

/-- On the chart source, the fiber coordinate of `orbitMapTrivialization` is
`s (g • x₀)⁻¹ * g`. -/
@[simp]
theorem orbitMapTrivialization_fiberCoordinate {g : G} (hg : g • x₀ ∈ U) :
    ((orbitMapTrivialization x₀ hx₀ U hU s hs hsec g).2 : G) = (s (g • x₀))⁻¹ * g :=
  Subgroup.localSectionTrivializationOfCosetFibers_fiberCoordinate (K := stabilizer G x₀) hg

/-- The inverse of `orbitMapTrivialization` reconstructs a group element by multiplying the
section by the fiber. -/
@[simp]
theorem orbitMapTrivialization_symm_apply (p : X × stabilizer G x₀) :
    (orbitMapTrivialization x₀ hx₀ U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 * p.2 :=
  Subgroup.localSectionTrivializationOfCosetFibers_symm_apply p

/-- `orbitMapTrivialization` intertwines right multiplication by the stabilizer of `x₀` on `G`
with right multiplication on the fibre. -/
theorem orbitMapTrivialization_apply_mul {g : G} (hg : g • x₀ ∈ U) (h : stabilizer G x₀) :
    orbitMapTrivialization x₀ hx₀ U hU s hs hsec (g * h) =
      ((orbitMapTrivialization x₀ hx₀ U hU s hs hsec g).1,
        (orbitMapTrivialization x₀ hx₀ U hU s hs hsec g).2 * h) :=
  Subgroup.localSectionTrivializationOfCosetFibers_apply_mul (K := stabilizer G x₀) hg h

end TauCeti

/-! ### Equivariant maps to a space with local sections of an orbit map -/

namespace TauCeti

variable {G E X : Type*} [Group G] [MulAction G E] [MulAction G X]

/-- A point of the fibre of an equivariant map over `s z • x₀ = z` is carried by `(s z)⁻¹` into
the fibre over `x₀`. -/
private theorem equivariant_inv_smul_mem {p : E → X}
    (hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e) {x₀ : X} {s : X → G} {e : E}
    (hsec : s (p e) • x₀ = p e) : p ((s (p e))⁻¹ • e) = x₀ := by
  rw [hp_smul, inv_smul_eq_iff, hsec]

/-- The fibre coordinate of `equivariantTrivialization`: over `U` it is `s (p e)⁻¹ • e`, and
elsewhere it is an arbitrary point of the fibre over `x₀`. -/
private noncomputable def equivariantFiberCoord {p : E → X}
    (hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e) {x₀ : X} (hx₀ : ∃ e, p e = x₀)
    (U : Set X) (s : X → G) (hsec : ∀ z ∈ U, s z • x₀ = z) (e : E) : {e : E // p e = x₀} := by
  classical
  exact ⟨if p e ∈ U then (s (p e))⁻¹ • e else hx₀.choose, by
    split_ifs with h
    exacts [equivariant_inv_smul_mem hp_smul (hsec _ h), hx₀.choose_spec]⟩

private theorem coe_equivariantFiberCoord {p : E → X}
    {hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e} {x₀ : X} {hx₀ : ∃ e, p e = x₀}
    {U : Set X} {s : X → G} {hsec : ∀ z ∈ U, s z • x₀ = z} {e : E} (he : p e ∈ U) :
    (equivariantFiberCoord hp_smul hx₀ U s hsec e : E) = (s (p e))⁻¹ • e := by
  simp [equivariantFiberCoord, he]

variable [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace E] [ContinuousSMul G E]
  [TopologicalSpace X]

private theorem continuousOn_equivariantFiberCoord {p : E → X} (hp : Continuous p)
    {hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e} {x₀ : X} {hx₀ : ∃ e, p e = x₀}
    {U : Set X} {s : X → G} (hs : ContinuousOn s U) {hsec : ∀ z ∈ U, s z • x₀ = z} :
    ContinuousOn (equivariantFiberCoord hp_smul hx₀ U s hsec) (p ⁻¹' U) := by
  refine Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.2 ?_
  exact (((hs.comp hp.continuousOn fun _ he ↦ he).inv).smul continuousOn_id).congr
    fun e he ↦ coe_equivariantFiberCoord he

/-- Let `p : E → X` be a continuous map that is equivariant for actions of `G`, and let `s` be a
section of the orbit map `g ↦ g • x₀`, continuous on an open set `U`. Then `p` is trivial over `U`
with fibre `p⁻¹(x₀)`: the chart sends `e` over `U` to `(p e, s (p e)⁻¹ • e)`, and its inverse sends
`(z, y)` to `s z • y`. The fibre over `x₀` is assumed nonempty, since a chart is a total map. -/
noncomputable def equivariantTrivialization (p : E → X) (hp : Continuous p)
    (hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e) {x₀ : X} (hx₀ : ∃ e, p e = x₀)
    (U : Set X) (hU : IsOpen U) (s : X → G) (hs : ContinuousOn s U)
    (hsec : ∀ z ∈ U, s z • x₀ = z) :
    Trivialization {e : E // p e = x₀} p where
  toFun e := (p e, equivariantFiberCoord hp_smul hx₀ U s hsec e)
  invFun q := s q.1 • (q.2 : E)
  source := p ⁻¹' U
  target := U ×ˢ univ
  map_source' _ he := ⟨he, mem_univ _⟩
  map_target' q hq := by
    simpa only [mem_preimage, hp_smul, q.2.2, hsec q.1 (mem_prod.1 hq).1] using (mem_prod.1 hq).1
  left_inv' e he := by
    simp [coe_equivariantFiberCoord (mem_preimage.1 he)]
  right_inv' q hq := by
    have hq' : p (s q.1 • (q.2 : E)) = q.1 := by rw [hp_smul, q.2.2, hsec q.1 (mem_prod.1 hq).1]
    refine Prod.ext hq' (Subtype.ext ?_)
    simp [coe_equivariantFiberCoord (hq'.symm ▸ (mem_prod.1 hq).1 : p (s q.1 • (q.2 : E)) ∈ U),
      hq']
  open_source := hU.preimage hp
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := hp.continuousOn.prodMk (continuousOn_equivariantFiberCoord hp hs)
  continuousOn_invFun :=
    (hs.comp continuousOn_fst fun _ hq ↦ (mem_prod.1 hq).1).smul
      (continuous_subtype_val.comp continuous_snd).continuousOn
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {p : E → X} {hp : Continuous p} {hp_smul : ∀ (g : G) (e : E), p (g • e) = g • p e}
  {x₀ : X} {hx₀ : ∃ e, p e = x₀} {U : Set X} {hU : IsOpen U} {s : X → G} {hs : ContinuousOn s U}
  {hsec : ∀ z ∈ U, s z • x₀ = z}

/-- The base of `equivariantTrivialization` is the domain of the local section. -/
@[simp]
theorem equivariantTrivialization_baseSet :
    (equivariantTrivialization p hp hp_smul hx₀ U hU s hs hsec).baseSet = U :=
  (rfl)

/-- The base coordinate of `equivariantTrivialization` is `p`. -/
@[simp]
theorem equivariantTrivialization_apply_fst (e : E) :
    (equivariantTrivialization p hp hp_smul hx₀ U hU s hs hsec e).1 = p e :=
  (rfl)

/-- Over the base, the fibre coordinate of `equivariantTrivialization` is `s (p e)⁻¹ • e`. -/
@[simp]
theorem coe_equivariantTrivialization_apply_snd {e : E} (he : p e ∈ U) :
    ((equivariantTrivialization p hp hp_smul hx₀ U hU s hs hsec e).2 : E) = (s (p e))⁻¹ • e :=
  coe_equivariantFiberCoord (hp_smul := hp_smul) (hsec := hsec) he

/-- The inverse of `equivariantTrivialization` moves a point of the fibre over `x₀` by the
section. -/
@[simp]
theorem equivariantTrivialization_symm_apply (q : X × {e : E // p e = x₀}) :
    (equivariantTrivialization p hp hp_smul hx₀ U hU s hs hsec).toOpenPartialHomeomorph.symm q =
      s q.1 • (q.2 : E) :=
  (rfl)

end TauCeti
