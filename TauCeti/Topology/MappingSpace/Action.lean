/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Group actions on mapping spaces and local triviality of evaluation

Let a topological group `G` act continuously on a space `X`, and fix a point `x₀ : X` and a
pointed space `(B, b₀)`. Then `G` acts on the mapping space `Map(B, X) = C(B, X)` by
postcomposition, and the stabilizer `H` of `x₀` acts on the based mapping space
`Map_*(B, X)` of maps sending `b₀` to `x₀` (`TauCeti.BasedMap.instMulActionStabilizer`). The
**action map**

`Φ : G × Map_*(B, X) → Map(B, X)`, `(g, u) ↦ g ∘ u`

(`TauCeti.mappingSpaceAction`) is a map over `X` from `G × Map_*(B, X)`, projected to `X` by
`(g, u) ↦ g • x₀`, to `Map(B, X)`, projected by evaluation at `b₀`
(`TauCeti.mappingSpaceEval_mappingSpaceAction`). On the fibres over `x₀` it restricts to the
action `H × Map_*(B, X) → Map_*(B, X)` of the stabilizer
(`TauCeti.mappingSpaceAction_stabilizer`), and it identifies `Map(B, X)` over the orbit of `x₀`
with the balanced product `G ×_H Map_*(B, X)`: it is `H`-balanced
(`TauCeti.mappingSpaceAction_mul_stabilizer`), two pairs have the same image exactly when they
differ by an element of `H` (`TauCeti.mappingSpaceAction_eq_mappingSpaceAction_iff`), and its
image consists of the maps sending `b₀` into the orbit of `x₀`
(`TauCeti.mem_range_mappingSpaceAction_iff`).

For `B = S²` this is the map of fibrations
`(H ↪ G → G • x₀) → (Ω²X ↪ Map(S², X) → X)` through which Barraud–Damian–Humilière–Oancea
compare homology classes of a transformation group with classes of `Map(S², X)`: for the
diffeomorphism group of a manifold (their Proposition 6.29) and for a homogeneous space `G ⧸ H`
with the stabilizer `H` of the base coset (their Proposition 6.36).

A continuous local section `s` of the orbit map `g ↦ g • x₀` over an open set `U` gives a
trivialization of evaluation `Map(B, X) → X` over `U` with fibre `Map_*(B, X)`
(`TauCeti.mappingSpaceEvalTrivialization`): it sends `f` to `(f b₀, s (f b₀)⁻¹ • f)`, with inverse
`(z, u) ↦ s z • u`. In these charts and the corresponding charts
`TauCeti.orbitMapTrivialization` of the orbit map, the action map is the action of the stabilizer
on the fibre (`TauCeti.mappingSpaceEvalTrivialization_mappingSpaceAction`). So if the orbit map
has local sections around every point of `X`, evaluation is locally trivial and hence a Serre
fibration (`TauCeti.TopCat.mappingSpaceEval_mem_serreFibrations_of_localSection`), for every
pointed space `(B, b₀)`: no cofibration condition on the base point and no compactness of `B`
is needed.

## Main definitions

* `TauCeti.BasedMap.instMulActionStabilizer`: the stabilizer of `x₀` acts continuously on
  `Map_*(B, X)` by postcomposition.
* `TauCeti.mappingSpaceAction`: the action map `G × Map_*(B, X) → Map(B, X)`.
* `TauCeti.mappingSpaceEvalTrivialization`: the trivialization of evaluation determined by a
  local section of the orbit map.

## Main results

* `TauCeti.mappingSpaceEval_mappingSpaceAction`: the action map lies over `X`.
* `TauCeti.mappingSpaceAction_stabilizer`: on the fibres over `x₀` it is the action of the
  stabilizer.
* `TauCeti.mappingSpaceAction_eq_mappingSpaceAction_iff` and
  `TauCeti.mem_range_mappingSpaceAction_iff`: its fibres are the orbits of the stabilizer, and its
  image is the set of maps sending `b₀` into the orbit of `x₀`.
* `TauCeti.mappingSpaceEvalTrivialization_mappingSpaceAction`: in local charts the action map is
  the action of the stabilizer on the fibre.
* `TauCeti.TopCat.mappingSpaceEval_mem_serreFibrations_of_localSection`: evaluation is a Serre
  fibration when the orbit map has local sections everywhere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, proofs of Propositions 6.29 and
  6.36.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Bundle MulAction Set Topology

namespace TauCeti

universe u

variable {G B X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X] {b₀ : B} {x₀ : X}

/-! ### The action of the stabilizer on based maps -/

namespace BasedMap

/-- The stabilizer of `x₀` acts on the maps sending `b₀` to `x₀` by postcomposition. -/
instance instMulActionStabilizer : MulAction (stabilizer G x₀) (BasedMap B X b₀ x₀) where
  smul h u := ⟨(h : G) • u.1, by
    rw [ContinuousMap.smul_apply, u.2, mem_stabilizer_iff.1 h.2]⟩
  one_smul u := Subtype.ext (one_smul G u.1)
  mul_smul h k u := Subtype.ext (mul_smul (h : G) (k : G) u.1)

/-- The stabilizer acts on based maps through the action of `G` on all maps. -/
@[simp]
theorem coe_stabilizer_smul (h : stabilizer G x₀) (u : BasedMap B X b₀ x₀) :
    (h • u).1 = (h : G) • u.1 :=
  (rfl)

/-- The action of the stabilizer on based maps is continuous. -/
instance instContinuousSMulStabilizer :
    ContinuousSMul (stabilizer G x₀) (BasedMap B X b₀ x₀) where
  continuous_smul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)

end BasedMap

/-! ### The action map -/

variable (b₀ x₀) in
/-- The **action map** `G × Map_*(B, X) → Map(B, X)`, `(g, u) ↦ g ∘ u`, of a group acting on
the target. Projecting its source to `X` by `(g, u) ↦ g • x₀` and its target by evaluation at
`b₀` makes it a map over `X` (`TauCeti.mappingSpaceEval_mappingSpaceAction`). -/
def mappingSpaceAction : C(G × BasedMap B X b₀ x₀, C(B, X)) :=
  ⟨fun p ↦ p.1 • p.2.1, continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩

/-- The action map composes a based map with a group element. -/
@[simp]
theorem mappingSpaceAction_apply (g : G) (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ (g, u) = g • u.1 :=
  (rfl)

/-- **The action map lies over `X`**: evaluating `g ∘ u` at `b₀` gives `g • x₀`. -/
theorem mappingSpaceEval_mappingSpaceAction (p : G × BasedMap B X b₀ x₀) :
    mappingSpaceEval b₀ (mappingSpaceAction b₀ x₀ p) = p.1 • x₀ := by
  rw [mappingSpaceEval_apply, mappingSpaceAction_apply, ContinuousMap.smul_apply, p.2.2]

/-- The action map at the identity is the inclusion of the based maps. -/
theorem mappingSpaceAction_one (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ ((1 : G), u) = u.1 := by
  simp

/-- The action map is equivariant for left multiplication on `G`. -/
theorem mappingSpaceAction_mul (g g' : G) (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ (g * g', u) = g • mappingSpaceAction b₀ x₀ (g', u) := by
  simp [mul_smul]

/-- **The action map is balanced** over the stabilizer `H` of `x₀`: `(g h) ∘ u = g ∘ (h ∘ u)`, so
it factors through `G ×_H Map_*(B, X)`. -/
theorem mappingSpaceAction_mul_stabilizer (g : G) (h : stabilizer G x₀)
    (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ (g * h, u) = mappingSpaceAction b₀ x₀ (g, h • u) := by
  simp [mul_smul]

/-- **On the fibres over `x₀` the action map is the action of the stabilizer** on based maps. -/
theorem mappingSpaceAction_stabilizer (h : stabilizer G x₀) (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ ((h : G), u) = (h • u).1 :=
  (rfl)

/-- The action map sends `(g, u)` to a map based at `x₀` exactly when `g` lies in the stabilizer
of `x₀`. -/
theorem mappingSpaceAction_apply_eq_iff (g : G) (u : BasedMap B X b₀ x₀) :
    mappingSpaceAction b₀ x₀ (g, u) b₀ = x₀ ↔ g ∈ stabilizer G x₀ := by
  rw [mem_stabilizer_iff, ← mappingSpaceEval_mappingSpaceAction (g, u), mappingSpaceEval_apply]

/-- **The fibres of the action map are the orbits of the stabilizer**: `g ∘ u = g' ∘ u'` exactly
when `g' = g h` and `u = h ∘ u'` for some `h` in the stabilizer of `x₀`. -/
theorem mappingSpaceAction_eq_mappingSpaceAction_iff {g g' : G} {u u' : BasedMap B X b₀ x₀} :
    mappingSpaceAction b₀ x₀ (g, u) = mappingSpaceAction b₀ x₀ (g', u') ↔
      ∃ h : stabilizer G x₀, g' = g * h ∧ u = h • u' := by
  constructor
  · intro hgu
    have hx : g • x₀ = g' • x₀ := by
      simpa [u.2, u'.2] using congrArg (mappingSpaceEval b₀) hgu
    refine ⟨⟨g⁻¹ * g', mem_stabilizer_iff.2 ?_⟩, by simp, Subtype.ext ?_⟩
    · rw [mul_smul, ← hx, inv_smul_smul]
    · rw [BasedMap.coe_stabilizer_smul, mul_smul, ← mappingSpaceAction_apply g' u', ← hgu,
        mappingSpaceAction_apply, inv_smul_smul]
  · rintro ⟨h, rfl, rfl⟩
    exact (mappingSpaceAction_mul_stabilizer g h u').symm

/-- **The image of the action map** consists of the maps sending `b₀` into the orbit of `x₀`. -/
theorem mem_range_mappingSpaceAction_iff (f : C(B, X)) :
    f ∈ range (mappingSpaceAction b₀ x₀ (G := G)) ↔ f b₀ ∈ orbit G x₀ := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, by rw [← mappingSpaceEval_apply b₀, mappingSpaceEval_mappingSpaceAction]⟩
  · rintro ⟨g, hg⟩
    refine ⟨(g, ⟨g⁻¹ • f, ?_⟩), ?_⟩
    · rw [ContinuousMap.smul_apply, ← hg, inv_smul_smul]
    · simp

/-! ### Local triviality of evaluation -/

section Trivialization

variable [ContinuousInv G] {U : Set X} {s : X → G}

variable (b₀ x₀ U s) in
/-- The fibre coordinate of `TauCeti.mappingSpaceEvalTrivialization`: over `U` it translates a
map `f` back to `x₀` by `s (f b₀)⁻¹`, and elsewhere it is the constant map. -/
private noncomputable def mappingSpaceEvalFiber (hsec : ∀ z ∈ U, s z • x₀ = z) (f : C(B, X)) :
    BasedMap B X b₀ x₀ :=
  letI := Classical.dec (f b₀ ∈ U)
  if hf : f b₀ ∈ U then
    ⟨(s (f b₀))⁻¹ • f, by rw [ContinuousMap.smul_apply, inv_smul_eq_iff, hsec _ hf]⟩
  else ⟨ContinuousMap.const B x₀, rfl⟩

omit [ContinuousInv G] in
private theorem coe_mappingSpaceEvalFiber {hsec : ∀ z ∈ U, s z • x₀ = z} {f : C(B, X)}
    (hf : f b₀ ∈ U) :
    (mappingSpaceEvalFiber b₀ x₀ U s hsec f).1 = (s (f b₀))⁻¹ • f := by
  simp only [mappingSpaceEvalFiber, hf, ↓reduceDIte]

variable (b₀ x₀) in
/-- **Local triviality of evaluation from a local section of the orbit map.** A section `s` of
the orbit map `g ↦ g • x₀`, continuous on an open set `U`, trivializes evaluation
`Map(B, X) → X` at `b₀` over `U`, with fibre the based mapping space `Map_*(B, X)`: the chart sends
`f` to `(f b₀, s (f b₀)⁻¹ • f)`, and its inverse sends `(z, u)` to `s z • u`. -/
noncomputable def mappingSpaceEvalTrivialization (U : Set X) (hU : IsOpen U) (s : X → G)
    (hs : ContinuousOn s U) (hsec : ∀ z ∈ U, s z • x₀ = z) :
    Trivialization (BasedMap B X b₀ x₀) (mappingSpaceEval (X := X) b₀) where
  toFun f := (mappingSpaceEval b₀ f, mappingSpaceEvalFiber b₀ x₀ U s hsec f)
  invFun p := s p.1 • p.2.1
  source := mappingSpaceEval b₀ ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hf := ⟨hf, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, mappingSpaceEval_apply, ContinuousMap.smul_apply, p.2.2, hsec _ hp.1]
    exact hp.1
  left_inv' f hf := by
    rw [mem_preimage, mappingSpaceEval_apply] at hf
    rw [mappingSpaceEval_apply, coe_mappingSpaceEvalFiber hf, smul_inv_smul]
  right_inv' p hp := by
    have hp' : (s p.1 • p.2.1) b₀ = p.1 := by
      rw [ContinuousMap.smul_apply, p.2.2, hsec _ hp.1]
    refine Prod.ext ((mappingSpaceEval_apply _ _).trans hp') (Subtype.ext ?_)
    rw [coe_mappingSpaceEvalFiber (hp'.symm ▸ hp.1), hp', inv_smul_smul]
  open_source := hU.preimage (mappingSpaceEval b₀).continuous
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine (mappingSpaceEval b₀).continuous.continuousOn.prodMk ?_
    refine (IsInducing.subtypeVal (t := {g : C(B, X) | g b₀ = x₀})).continuousOn_iff.2 ?_
    refine (((hs.comp (mappingSpaceEval b₀).continuous.continuousOn fun _ hf ↦ hf).inv).smul
      continuousOn_id).congr fun f hf ↦ ?_
    rw [mem_preimage, mappingSpaceEval_apply] at hf
    rw [Function.comp_apply, coe_mappingSpaceEvalFiber hf, Pi.smul_apply', Pi.inv_apply,
      Function.comp_apply, mappingSpaceEval_apply, id]
  continuousOn_invFun :=
    (hs.comp (continuousOn_fst (s := U ×ˢ univ)) fun _ hp ↦ hp.1).smul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd)
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hU : IsOpen U} {hs : ContinuousOn s U} {hsec : ∀ z ∈ U, s z • x₀ = z}

/-- The base of `TauCeti.mappingSpaceEvalTrivialization` is the domain of the local section. -/
@[simp]
theorem mappingSpaceEvalTrivialization_baseSet :
    (mappingSpaceEvalTrivialization b₀ x₀ U hU s hs hsec).baseSet = U :=
  (rfl)

/-- On the chart source, `TauCeti.mappingSpaceEvalTrivialization` sends `f` to
`(f b₀, s (f b₀)⁻¹ • f)`. -/
@[simp]
theorem mappingSpaceEvalTrivialization_apply {f : C(B, X)} (hf : f b₀ ∈ U) :
    mappingSpaceEvalTrivialization b₀ x₀ U hU s hs hsec f =
      (f b₀, ⟨(s (f b₀))⁻¹ • f, by rw [ContinuousMap.smul_apply, inv_smul_eq_iff, hsec _ hf]⟩) :=
  Prod.ext (mappingSpaceEval_apply _ _) (Subtype.ext (coe_mappingSpaceEvalFiber (hsec := hsec) hf))

/-- The inverse of `TauCeti.mappingSpaceEvalTrivialization` sends `(z, u)` to `s z • u`. -/
@[simp]
theorem mappingSpaceEvalTrivialization_symm_apply (p : X × BasedMap B X b₀ x₀) :
    (mappingSpaceEvalTrivialization b₀ x₀ U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 • p.2.1 :=
  (rfl)

/-- **In local charts the action map is the action of the stabilizer on the fibre.** If
`g • x₀ ∈ U`, the charts of evaluation and of the orbit map determined by the same section `s`
send `g ∘ u` and `g` to `(g • x₀, h • u)` and `(g • x₀, h)` with the same `h`
in the stabilizer. -/
theorem mappingSpaceEvalTrivialization_mappingSpaceAction [ContinuousMul G]
    {hx₀ : Continuous fun g : G ↦ g • x₀} {g : G} (hg : g • x₀ ∈ U) (u : BasedMap B X b₀ x₀) :
    mappingSpaceEvalTrivialization b₀ x₀ U hU s hs hsec (mappingSpaceAction b₀ x₀ (g, u)) =
      ((orbitMapTrivialization x₀ hx₀ U hU s hs hsec g).1,
        (orbitMapTrivialization x₀ hx₀ U hU s hs hsec g).2 • u) := by
  have hsrc : g ∈ (orbitMapTrivialization x₀ hx₀ U hU s hs hsec).source := by
    rw [Trivialization.mem_source, orbitMapTrivialization_baseSet]
    exact hg
  have hgu : mappingSpaceAction b₀ x₀ (g, u) b₀ ∈ U := by
    rwa [mappingSpaceAction_apply, ContinuousMap.smul_apply, u.2]
  rw [mappingSpaceEvalTrivialization_apply hgu,
    (orbitMapTrivialization x₀ hx₀ U hU s hs hsec).coe_fst hsrc]
  refine Prod.ext (by simp [u.2]) (Subtype.ext ?_)
  rw [BasedMap.coe_stabilizer_smul, orbitMapTrivialization_fiberCoordinate hg]
  simp [u.2, mul_smul]

end Trivialization

/-- **Evaluation is locally trivial when the orbit map has local sections.** If around every point
of `X` the orbit map `g ↦ g • x₀` has a section continuous on an open neighbourhood, then
evaluation `Map(B, X) → X` at `b₀` has a trivialization with fibre `Map_*(B, X)` around every
point. -/
theorem exists_trivialization_mappingSpaceEval_of_localSection [ContinuousInv G]
    (h : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ ∃ s : X → G, ContinuousOn s U ∧
      ∀ y ∈ U, s y • x₀ = y) (z : X) :
    ∃ e : Trivialization (BasedMap B X b₀ x₀) (mappingSpaceEval (X := X) b₀), z ∈ e.baseSet := by
  obtain ⟨U, hU, hzU, s, hs, hsec⟩ := h z
  exact ⟨mappingSpaceEvalTrivialization b₀ x₀ U hU s hs hsec, hzU⟩

/-- **Evaluation is a Serre fibration when the orbit map has local sections.** If around every
point of `X` the orbit map `g ↦ g • x₀` has a section continuous on an open neighbourhood, then
evaluation `Map(B, X) → X` at any point `b₀` of any space `B` is a Serre fibration. -/
theorem TopCat.mappingSpaceEval_mem_serreFibrations_of_localSection {B X : Type u}
    [TopologicalSpace B] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [ContinuousInv G]
    (b₀ : B) {x₀ : X}
    (h : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ ∃ s : X → G, ContinuousOn s U ∧
      ∀ y ∈ U, s y • x₀ = y) :
    TopCat.serreFibrations (TopCat.ofHom (mappingSpaceEval (X := X) b₀)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization_mappingSpaceEval_of_localSection (b₀ := b₀) h)

end TauCeti
