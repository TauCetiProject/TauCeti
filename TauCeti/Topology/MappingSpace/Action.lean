/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Group actions on mapping spaces and the evaluation fibration of a homogeneous space

Let a topological group `G` act continuously on a space `X`, and let `B` be a space with a
basepoint `b₀`. Then `G` acts on the mapping space `Map(B, X)` pointwise, `(g • f)(b) = g • f(b)`;
this is Mathlib's action `ContinuousMap.instSMul`, jointly continuous for the compact-open topology.
Evaluation at the basepoint `ev : Map(B, X) → X` is equivariant
(`ContinuousMap.smul_apply`). Its fibre over a point `x` is the based mapping space
`Map_*(B, X)` of maps sending `b₀` to `x`, and the stabilizer of `x` acts continuously on that
fibre (`TauCeti.BasedMap.instMulActionStabilizer`, `TauCeti.BasedMap.instContinuousSMulStabilizer`).

The action restricted to `G × Map_*(B, X)` (`TauCeti.BasedMap.actionMap`) is a map of fibrations:
it lies over the orbit map `g ↦ g • x` (`TauCeti.mappingSpaceEval_actionMap`), and on the fibre
over `x` of the orbit map, the stabilizer, it is the action of the stabilizer on the based mapping
space (`TauCeti.BasedMap.coe_stabilizer_smul`). For a homogeneous space `X = G ⧸ H` and `B = S²`
these are the actions `Φ : G × Map(S², G ⧸ H) → Map(S², G ⧸ H)` and
`Φ_H : H × Ω²(G ⧸ H) → Ω²(G ⧸ H)` of Barraud–Damian–Humilière–Oancea, Proposition 6.36: the
stabilizer of the coset `eH` is `H` (`MulAction.stabilizer_quotient`).

A continuous local section `s` of the orbit map over an open set `U`, `s y • x = y` for `y ∈ U`,
translates every map with `f(b₀) ∈ U` to a based map: `f ↦ (f(b₀), s(f(b₀))⁻¹ • f)` is a local
trivialization of evaluation over `U` with fibre `Map_*(B, X)`, with inverse
`(y, γ) ↦ s(y) • γ` (`TauCeti.mappingSpaceEvalTrivialization`). This generalizes the global
product decomposition `G × Map_*(B, G) ≃ₜ Map(B, G)` of maps into a group
(`TauCeti.mappingSpaceGroupHomeomorph`), where the section is the identity. So if the orbit map
has continuous local sections around every point, then evaluation is locally trivial with fibre
`Map_*(B, X)`. It is then a Serre fibration (`TauCeti.mappingSpaceEval_mem_serreFibrations`),
and a Hurewicz fibration over a normal paracompact space
(`TauCeti.isHurewiczFibration_mappingSpaceEval`). For `X = G ⧸ H` a local section of the
quotient map is a local section of the orbit map of `eH`
(`TauCeti.mappingSpaceEval_mem_serreFibrations_quotient`).

No compactness or separation assumption is made on `B`.

## Main declarations

* `TauCeti.BasedMap.instMulActionStabilizer`: the stabilizer of `x` acts on `Map_*(B, X)`.
* `TauCeti.BasedMap.actionMap`: the action map `G × Map_*(B, X) → Map(B, X)`.
* `TauCeti.mappingSpaceEvalTrivialization`: the local trivialization of evaluation given by a
  local section of the orbit map.

## Main results

* `TauCeti.mappingSpaceEval_actionMap`: the action map lies over the orbit map.
* `TauCeti.exists_trivialization_mappingSpaceEval`: evaluation is locally trivial when the orbit
  map has local sections.
* `TauCeti.mappingSpaceEval_mem_serreFibrations`,
  `TauCeti.isHurewiczFibration_mappingSpaceEval`: evaluation is then a Serre fibration, and a
  Hurewicz fibration over a normal paracompact space.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, Proposition 6.36.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

noncomputable section

open Set Topology MulAction

namespace TauCeti

universe u v w

section General

variable {G : Type*} {B : Type u} {X : Type v} [Group G] [TopologicalSpace B]
  [TopologicalSpace X] [MulAction G X]

/-! ### The stabilizer action on based maps -/

section Action

variable [ContinuousConstSMul G X]

namespace BasedMap

variable {b₀ : B} {x : X}

/-- The stabilizer of `x` acts pointwise on the maps sending the basepoint to `x`. -/
instance instSMulStabilizer : SMul (stabilizer G x) (BasedMap B X b₀ x) where
  smul h f := ⟨(h : G) • f.1, by
    rw [ContinuousMap.smul_apply, f.2]
    exact mem_stabilizer_iff.1 h.2⟩

/-- The action of the stabilizer on based maps is the pointwise action. -/
@[simp]
theorem coe_stabilizer_smul (h : stabilizer G x) (f : BasedMap B X b₀ x) :
    ((h • f : BasedMap B X b₀ x) : C(B, X)) = (h : G) • (f : C(B, X)) :=
  (rfl)

/-- The stabilizer of `x` acts on the based mapping space `Map_*(B, X)`. For a homogeneous space
`G ⧸ H` and `x` the coset `eH`, the stabilizer is `H` (`MulAction.stabilizer_quotient`). -/
instance instMulActionStabilizer : MulAction (stabilizer G x) (BasedMap B X b₀ x) where
  one_smul f := Subtype.ext (one_smul G f.1)
  mul_smul h k f := Subtype.ext (mul_smul (h : G) (k : G) f.1)

end BasedMap

end Action

section ContinuousAction

variable [TopologicalSpace G] [ContinuousSMul G X]

namespace BasedMap

variable {b₀ : B} {x : X}

/-- The action of the stabilizer on the based mapping space is jointly continuous. -/
instance instContinuousSMulStabilizer :
    ContinuousSMul (stabilizer G x) (BasedMap B X b₀ x) where
  continuous_smul :=
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-! ### The action map as a map of fibrations -/

variable (b₀ x) in
/-- The action map `G × Map_*(B, X) → Map(B, X)`, `(g, γ) ↦ g • γ`. It lies over the orbit map
`g ↦ g • x` (`TauCeti.mappingSpaceEval_actionMap`), and on the stabilizer it is the action of the
stabilizer on based maps (`TauCeti.BasedMap.coe_stabilizer_smul`). -/
def actionMap : C(G × BasedMap B X b₀ x, C(B, X)) :=
  ⟨fun p ↦ p.1 • p.2.1, continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩

/-- The action map translates a based map by the group element. -/
@[simp]
theorem actionMap_apply (p : G × BasedMap B X b₀ x) : actionMap b₀ x p = p.1 • p.2.1 :=
  (rfl)

end BasedMap

/-- The action map lies over the orbit map: evaluating `g • γ` at the basepoint gives `g • x`. -/
theorem mappingSpaceEval_actionMap {b₀ : B} {x : X}
    (p : G × BasedMap B X b₀ x) :
    mappingSpaceEval b₀ (BasedMap.actionMap b₀ x p) = p.1 • x := by
  rw [BasedMap.actionMap_apply, mappingSpaceEval_apply, ContinuousMap.smul_apply, p.2.2]

/-! ### Local triviality of evaluation -/

section Trivialization

variable [ContinuousInv G] (b₀ : B) (x : X)

/-- The based map `s(f(b₀))⁻¹ • f` when `f(b₀)` lies in the domain `U` of the local section `s`,
and the constant map otherwise. -/
private def sectionTranslate (U : Set X) (s : X → G) (hsec : ∀ y ∈ U, s y • x = y)
    (f : C(B, X)) : BasedMap B X b₀ x :=
  letI := Classical.dec (f b₀ ∈ U)
  if hf : f b₀ ∈ U then
    ⟨(s (f b₀))⁻¹ • f, by
      rw [ContinuousMap.smul_apply, inv_smul_eq_iff]
      exact (hsec _ hf).symm⟩
  else ⟨ContinuousMap.const B x, rfl⟩

omit [ContinuousInv G] in
private theorem coe_sectionTranslate {U : Set X} {s : X → G} {hsec : ∀ y ∈ U, s y • x = y}
    {f : C(B, X)} (hf : f b₀ ∈ U) :
    (sectionTranslate b₀ x U s hsec f : C(B, X)) = (s (f b₀))⁻¹ • f := by
  simp only [sectionTranslate, hf, ↓reduceDIte]

/-- A section `s` of the orbit map `g ↦ g • x`, continuous on an open set `U`, defines a local
trivialization of evaluation at `b₀` over `U` with fibre the based mapping space: it sends a map
`f` with `f(b₀) ∈ U` to `(f(b₀), s(f(b₀))⁻¹ • f)`, and its inverse sends `(y, γ)` to
`s(y) • γ`. -/
def mappingSpaceEvalTrivialization (U : Set X) (hU : IsOpen U) (s : X → G)
    (hs : ContinuousOn s U) (hsec : ∀ y ∈ U, s y • x = y) :
    Bundle.Trivialization (BasedMap B X b₀ x) (mappingSpaceEval (X := X) b₀) where
  toFun f := (f b₀, sectionTranslate b₀ x U s hsec f)
  invFun p := s p.1 • p.2.1
  source := {f | f b₀ ∈ U}
  target := U ×ˢ univ
  map_source' _ hf := ⟨hf, mem_univ _⟩
  map_target' p hp := by
    change (s p.1 • p.2.1) b₀ ∈ U
    rw [ContinuousMap.smul_apply, p.2.2, hsec _ hp.1]
    exact hp.1
  left_inv' f hf := by
    change s (f b₀) • (sectionTranslate b₀ x U s hsec f : C(B, X)) = f
    rw [coe_sectionTranslate b₀ x hf, smul_inv_smul]
  right_inv' p hp := by
    have hp' : (s p.1 • p.2.1) b₀ = p.1 := by
      rw [ContinuousMap.smul_apply, p.2.2, hsec _ hp.1]
    refine Prod.ext hp' (Subtype.ext ?_)
    change (sectionTranslate b₀ x U s hsec (s p.1 • p.2.1) : C(B, X)) = p.2.1
    rw [coe_sectionTranslate b₀ x (hp'.symm ▸ hp.1 : (s p.1 • p.2.1) b₀ ∈ U), hp',
      inv_smul_smul]
  open_source := hU.preimage (continuous_eval_const b₀)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_eval_const b₀).continuousOn.prodMk ?_
    refine (IsEmbedding.subtypeVal (p := fun f : C(B, X) ↦ f b₀ = x)).isInducing.continuousOn_iff.2
      ?_
    exact ((hs.comp (continuous_eval_const b₀).continuousOn fun _ hf ↦ hf).inv.smul
      continuousOn_id).congr fun f hf ↦ coe_sectionTranslate b₀ x hf
  continuousOn_invFun :=
    (hs.comp (continuousOn_fst (s := U ×ˢ univ)) fun _ hp ↦ hp.1).smul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd)
  baseSet := U
  open_baseSet := hU
  source_eq := by ext; simp
  target_eq := rfl
  proj_toFun _ _ := (mappingSpaceEval_apply _ _).symm

variable {b₀ x} {U : Set X} {s : X → G} {hU : IsOpen U} {hs : ContinuousOn s U}
  {hsec : ∀ y ∈ U, s y • x = y}

/-- The base of `mappingSpaceEvalTrivialization` is the domain of the local section. -/
@[simp]
theorem mappingSpaceEvalTrivialization_baseSet :
    (mappingSpaceEvalTrivialization b₀ x U hU s hs hsec).baseSet = U :=
  (rfl)

/-- On the chart source, the fibre coordinate of `mappingSpaceEvalTrivialization` is the
translate `s(f(b₀))⁻¹ • f`. -/
@[simp]
theorem mappingSpaceEvalTrivialization_fiberCoordinate {f : C(B, X)} (hf : f b₀ ∈ U) :
    ((mappingSpaceEvalTrivialization b₀ x U hU s hs hsec f).2 : C(B, X)) = (s (f b₀))⁻¹ • f :=
  coe_sectionTranslate b₀ x (hsec := hsec) hf

/-- The inverse of `mappingSpaceEvalTrivialization` translates a based map by the local
section. -/
@[simp]
theorem mappingSpaceEvalTrivialization_symm_apply (p : X × BasedMap B X b₀ x) :
    (mappingSpaceEvalTrivialization b₀ x U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 • p.2.1 :=
  (rfl)

variable (b₀ x)

/-- If the orbit map `g ↦ g • x` has a continuous local section around every point, evaluation
at `b₀` is locally trivial with fibre the based mapping space `Map_*(B, X)`. -/
theorem exists_trivialization_mappingSpaceEval
    (h : ∀ y : X, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ ∃ s : X → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x = z) (y : X) :
    ∃ e : Bundle.Trivialization (BasedMap B X b₀ x) (mappingSpaceEval (X := X) b₀),
      y ∈ e.baseSet := by
  obtain ⟨U, hU, hy, s, hs, hsec⟩ := h y
  exact ⟨mappingSpaceEvalTrivialization b₀ x U hU s hs hsec, hy⟩

/-- If the orbit map `g ↦ g • x` has a continuous local section around every point, evaluation
at `b₀` is a Hurewicz fibration over a normal paracompact space. -/
theorem isHurewiczFibration_mappingSpaceEval [NormalSpace X] [ParacompactSpace X]
    (h : ∀ y : X, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ ∃ s : X → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x = z) :
    IsHurewiczFibration.{w} (mappingSpaceEval (X := X) b₀) :=
  isHurewiczFibration_of_exists_trivialization
    (exists_trivialization_mappingSpaceEval b₀ x h)

end Trivialization

end ContinuousAction

end General

section Serre

variable {G : Type*} {B X : Type u} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  [TopologicalSpace X] [MulAction G X] [ContinuousInv G] [ContinuousSMul G X] (b₀ : B)
  (x : X)

/-- If the orbit map `g ↦ g • x` has a continuous local section around every point, evaluation
at `b₀` is a Serre fibration, with fibre the based mapping space over `x`. -/
theorem mappingSpaceEval_mem_serreFibrations
    (h : ∀ y : X, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ ∃ s : X → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x = z) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom (mappingSpaceEval b₀) :
        _root_.TopCat.of C(B, X) ⟶ _root_.TopCat.of X) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization_mappingSpaceEval b₀ x h)

/-- **The evaluation fibration of a homogeneous space.** If the quotient map `K → K ⧸ H` has a
continuous local section around every point, evaluation at `b₀` on `Map(B, K ⧸ H)` is a Serre
fibration, with fibre over the coset `eH` the based mapping space `Map_*(B, K ⧸ H)`. The stabilizer
of `eH`, which is `H` by `MulAction.stabilizer_quotient`, acts on this fibre by
`TauCeti.BasedMap.instMulActionStabilizer`. -/
theorem mappingSpaceEval_mem_serreFibrations_quotient {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (H : Subgroup K)
    (h : ∀ q : K ⧸ H, ∃ U : Set (K ⧸ H), IsOpen U ∧ q ∈ U ∧ ∃ s : K ⧸ H → K,
      ContinuousOn s U ∧ ∀ q' ∈ U, (s q' : K ⧸ H) = q') :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom (mappingSpaceEval b₀) :
        _root_.TopCat.of C(B, K ⧸ H) ⟶ _root_.TopCat.of (K ⧸ H)) := by
  refine mappingSpaceEval_mem_serreFibrations (G := K) b₀ ((1 : K) : K ⧸ H) fun q ↦ ?_
  obtain ⟨U, hU, hq, s, hs, hsec⟩ := h q
  refine ⟨U, hU, hq, s, hs, fun q' hq' ↦ ?_⟩
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact hsec q' hq'

end Serre

end TauCeti
