/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerAlgebra.DiagramIdeal
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Equivariance
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.TraceSplitting
public import TauCeti.RepresentationTheory.Subrepresentation.Quotient
-- Non-public: the star-ordered ring structure on `ℚ`, for the two-strand check of the top graded
-- piece.
import Mathlib.Algebra.Order.Star.Rat

/-!
# The trace filtration of the orthogonal tensor powers

The Brauer algebra `B_d(n)` acts on `V^{⊗d}`, `V = kⁿ`, through the standard symmetric form
(`TauCeti.brauerActionOrth`), and it is filtered by its diagram ideals
`I_j = TauCeti.BrauerAlgebra.diagramIdeal k n d j`, the spans of the diagrams with at least `j`
caps. Pushing that filtration forward along the action filters the tensor power: the **trace
filtration** is

`F_j = span {ρ(b) v : b ∈ I_j, v ∈ V^{⊗d}}` (`TauCeti.orthogonalTraceFiltration k n d j`),

the tensors obtained by inserting at least `j` copies of the invariant form `∑ c, e_c ⊗ e_c`.
Its graded pieces `F_j / F_(j+1)` carry commuting actions of the orthogonal group and of the
Brauer algebra, and they are how Goodman and Wallach organize the tensor power on the Brauer side
of Schur-Weyl duality. Over a star-ordered field the top piece `F_0 / F_1` is a copy of the
harmonic tensors (`TauCeti.quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors`); the lower
pieces are not treated here.

Each `F_j` is a subrepresentation of the orthogonal group, because the Brauer algebra acts by
intertwiners, and it is stable under the whole Brauer algebra, because `I_j` is a left ideal.
The steps decrease, `F_0` is everything and `F_j = 0` once `2 * j > d`. Every element of `I_j`
maps the whole tensor power into `F_j`, so in particular `I_(j+1)` maps `F_j` into `F_(j+1)` and
acts by zero on the graded piece `F_j / F_(j+1)`.

The first step is the space of trace tensors `TauCeti.orthogonalTraceTensors k n d`, the sum of
the images of the single arcs (`TauCeti.orthogonalTraceFiltration_one`), over every commutative
ring. One inclusion holds because each arc is the action of a cap-cup diagram, which lies in
`I_1`. For the other, a diagram with a cap is a loop-free stack of a cap-cup diagram on another
diagram (`TauCeti.BrauerDiagram.exists_composeDiagram_capCup_eq`), so its action factors through
an arc. Over a star-ordered field such as `ℚ`, `ℝ` or `ℂ` the harmonic tensors therefore
complement `F_1`: rewriting by `TauCeti.orthogonalTraceFiltration_one` turns
`TauCeti.isCompl_harmonicTensorsSubrep_orthogonalTraceTensors` into this statement, so
`V^{⊗d}` is the direct sum of the harmonic tensors and `F_1` as a representation of the
orthogonal group, and the top graded piece `V^{⊗d} / F_1` is equivalent to the harmonic tensors
by `Subrepresentation.quotientEquivOfIsCompl`.

## Main definitions

* `TauCeti.orthogonalTraceFiltration`: the step `F_j` of the trace filtration, a
  subrepresentation of the orthogonal group acting on `V^{⊗d}`.
* `TauCeti.quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors`: over a star-ordered field,
  the top graded piece `V^{⊗d} / F_1` is equivalent to the harmonic tensors, as a representation
  of the orthogonal group.

## Main results

* `TauCeti.range_brauerActionOrth_le_orthogonalTraceFiltration` and
  `TauCeti.orthogonalTraceFiltration_toSubmodule_le_iff`: `F_j` contains the image of every
  element of `I_j`, and it is the least submodule doing so.
* `TauCeti.brauerActionOrth_apply_mem_orthogonalTraceFiltration`: `F_j` is stable under the
  Brauer algebra.
* `TauCeti.orthogonalTraceFiltration_zero`, `TauCeti.orthogonalTraceFiltration_antitone` and
  `TauCeti.orthogonalTraceFiltration_eq_bot`: `F_0` is everything, the steps decrease, and
  `F_j = 0` when `d < 2 * j`.
* `TauCeti.range_brauerActionOrth_le_orthogonalTraceTensors`: an element of `I_1` maps into the
  trace tensors.
* `TauCeti.orthogonalTraceFiltration_one`: **`F_1` is the space of trace tensors.**

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.2 and Appendix F, for the harmonic tensors and the trace filtration.
* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

universe u

namespace TauCeti

open BrauerAlgebra
open scoped TensorProduct

section CommRing

variable (k : Type u) [CommRing k] (n d : ℕ)

/-- **The trace filtration** of the orthogonal tensor power `V^{⊗d}`, `V = kⁿ`: its step `F_j` is
the sum of the images of the elements of the diagram ideal `I_j` of the Brauer algebra `B_d(n)`
acting through `TauCeti.brauerActionOrth`, that is, the span of the tensors obtained by inserting
at least `j` copies of the invariant form. It is a subrepresentation because the Brauer algebra
acts by intertwiners of the orthogonal group. -/
noncomputable def orthogonalTraceFiltration (j : ℕ) :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower d) where
  toSubmodule := ⨆ b ∈ diagramIdeal k (n : k) d j, LinearMap.range (brauerActionOrth k n d b)
  apply_mem_toSubmodule g := by
    suffices h : (⨆ b ∈ diagramIdeal k (n : k) d j, LinearMap.range (brauerActionOrth k n d b)) ≤
        Submodule.comap ((stdOrthogonalRep k n).tensorPower d g)
          (⨆ b ∈ diagramIdeal k (n : k) d j, LinearMap.range (brauerActionOrth k n d b))
      from fun x hx => h hx
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨y, rfl⟩
    have h := LinearMap.congr_fun (commute_brauerActionOrth_tensorPower k n d b g).eq y
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at h
    rw [Submodule.mem_comap, ← h]
    exact Submodule.mem_iSup_of_mem b <| Submodule.mem_iSup_of_mem hb <|
      LinearMap.mem_range_self _ _

@[simp]
theorem orthogonalTraceFiltration_toSubmodule (j : ℕ) :
    (orthogonalTraceFiltration k n d j).toSubmodule =
      ⨆ b ∈ diagramIdeal k (n : k) d j, LinearMap.range (brauerActionOrth k n d b) :=
  (rfl)

variable {k n d}

/-- The image of every element of the diagram ideal `I_j` lies in the step `F_j`. In particular,
`I_(j+1)` maps `F_j` into `F_(j+1)`, so it acts by zero on the graded piece `F_j / F_(j+1)`. -/
theorem range_brauerActionOrth_le_orthogonalTraceFiltration {j : ℕ}
    {b : BrauerAlgebra k (n : k) d} (hb : b ∈ diagramIdeal k (n : k) d j) :
    LinearMap.range (brauerActionOrth k n d b) ≤ (orthogonalTraceFiltration k n d j).toSubmodule :=
  le_iSup₂_of_le b hb le_rfl

/-- The order-level universal property: the step `F_j` lies in a submodule exactly when the image
of every element of `I_j` does. -/
theorem orthogonalTraceFiltration_toSubmodule_le_iff {j : ℕ}
    {p : Submodule k (⨂[k]^d (Fin n → k))} :
    (orthogonalTraceFiltration k n d j).toSubmodule ≤ p ↔
      ∀ b ∈ diagramIdeal k (n : k) d j, LinearMap.range (brauerActionOrth k n d b) ≤ p := by
  simp only [orthogonalTraceFiltration_toSubmodule, iSup_le_iff]

/-- **The steps of the trace filtration are stable under the Brauer algebra**, because the
diagram ideals are left ideals. -/
theorem brauerActionOrth_apply_mem_orthogonalTraceFiltration {j : ℕ}
    (b : BrauerAlgebra k (n : k) d) {x : ⨂[k]^d (Fin n → k)}
    (hx : x ∈ (orthogonalTraceFiltration k n d j).toSubmodule) :
    brauerActionOrth k n d b x ∈ (orthogonalTraceFiltration k n d j).toSubmodule := by
  suffices h : (orthogonalTraceFiltration k n d j).toSubmodule ≤
      Submodule.comap (brauerActionOrth k n d b) (orthogonalTraceFiltration k n d j).toSubmodule
    from h hx
  refine orthogonalTraceFiltration_toSubmodule_le_iff.mpr fun c hc => ?_
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_comap, ← mul_apply_eq_comp, ← map_mul]
  exact range_brauerActionOrth_le_orthogonalTraceFiltration
    ((diagramIdeal k (n : k) d j).mul_mem_left b c hc) (LinearMap.mem_range_self _ y)

variable (k n d)

/-- **The step `F_0` of the trace filtration is everything**: the unit of the Brauer algebra lies
in `I_0` and acts as the identity. -/
@[simp]
theorem orthogonalTraceFiltration_zero : orthogonalTraceFiltration k n d 0 = ⊤ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_top, eq_top_iff]
  intro x _
  have h := range_brauerActionOrth_le_orthogonalTraceFiltration (b := 1)
    (by rw [diagramIdeal_zero]; exact TwoSidedIdeal.mem_top _) (LinearMap.mem_range_self _ x)
  rwa [map_one, one_apply_eq_self] at h

/-- **The trace filtration decreases**, as the diagram ideals do. -/
theorem orthogonalTraceFiltration_antitone : Antitone (orthogonalTraceFiltration k n d) :=
  fun _ _ hij => Subrepresentation.toSubmodule_le_toSubmodule.mp <|
    orthogonalTraceFiltration_toSubmodule_le_iff.mpr fun _ hb =>
      range_brauerActionOrth_le_orthogonalTraceFiltration (diagramIdeal_antitone k _ d hij hb)

/-- **The trace filtration vanishes once `2 * j > d`**, as the diagram ideal `I_j` does: a
diagram on `d` strands has at most `d / 2` caps. -/
theorem orthogonalTraceFiltration_eq_bot {j : ℕ} (hj : d < 2 * j) :
    orthogonalTraceFiltration k n d j = ⊥ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_bot, eq_bot_iff, orthogonalTraceFiltration_toSubmodule_le_iff]
  intro b hb
  rw [diagramIdeal_eq_bot k _ d hj, TwoSidedIdeal.mem_bot] at hb
  simp [hb]

variable {k n d}

/-- **An element of `I_1` maps into the trace tensors.** A diagram with a cap is a loop-free
stack `capCup c e ∘ X` (`TauCeti.BrauerDiagram.exists_composeDiagram_capCup_eq`), so it acts as
the arc `TauCeti.orthogonalCupCapAt k n d c e` after the action of `X`, and its image lies in the
image of that arc. -/
theorem range_brauerActionOrth_le_orthogonalTraceTensors {b : BrauerAlgebra k (n : k) d}
    (hb : b ∈ diagramIdeal k (n : k) d 1) :
    LinearMap.range (brauerActionOrth k n d b) ≤ (orthogonalTraceTensors k n d).toSubmodule := by
  rw [mem_diagramIdeal_iff_mem_span] at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨D, hD, rfl⟩ := hx
    obtain ⟨a, ha⟩ : D.bottomCap.Nonempty := by
      rw [← Finset.card_pos]
      have := D.propagatingNumber_add_card_bottomCap
      simp only [Set.mem_ofPred_eq] at hD
      omega
    obtain ⟨c, e, X, hce, hloop, -, rfl⟩ := BrauerDiagram.exists_composeDiagram_capCup_eq ha
    rw [← of_mul_of_of_middleLoopCount_eq_zero hloop, map_mul, brauerActionOrth_of_capCup k n d hce,
      Module.End.mul_eq_comp, LinearMap.range_comp]
    exact LinearMap.map_le_range.trans (range_orthogonalCupCapAt_le_orthogonalTraceTensors hce)
  | zero => simp
  | add x y _ _ hx hy =>
    rintro _ ⟨v, rfl⟩
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hx (LinearMap.mem_range_self _ v)) (hy (LinearMap.mem_range_self _ v))
  | smul r x _ hx =>
    rintro _ ⟨v, rfl⟩
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ r (hx (LinearMap.mem_range_self _ v))

variable (k n d)

/-- **The first step of the trace filtration is the space of trace tensors**, over every
commutative ring: the tensors obtained from the elements of `I_1` are the sums of tensors
obtained by inserting the invariant form into a single pair of slots. Each arc
`TauCeti.orthogonalCupCapAt k n d i j` is the action of a cap-cup diagram, which lies in `I_1`;
conversely every element of `I_1` maps into the trace tensors
(`TauCeti.range_brauerActionOrth_le_orthogonalTraceTensors`). -/
theorem orthogonalTraceFiltration_one :
    orthogonalTraceFiltration k n d 1 = orthogonalTraceTensors k n d := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · exact orthogonalTraceFiltration_toSubmodule_le_iff.mpr fun _ hb =>
      range_brauerActionOrth_le_orthogonalTraceTensors hb
  · refine orthogonalTraceTensors_toSubmodule_le_iff.mpr fun i j hij => ?_
    rw [← brauerActionOrth_of_capCup k n d hij]
    exact range_brauerActionOrth_le_orthogonalTraceFiltration (of_capCup_mem_diagramIdeal_one hij)

end CommRing

/-! ### The top graded piece -/

section StarOrderedField

variable (k : Type u) [Field k] [PartialOrder k] [StarRing k] [StarOrderedRing k] (n d : ℕ)

/-- **The top graded piece of the trace filtration is the space of harmonic tensors.** Over a
star-ordered field, such as `ℚ`, `ℝ` or `ℂ` (with `ComplexOrder`), the quotient `V^{⊗d} / F_1` is
equivalent, as a representation of the orthogonal group, to the harmonic tensors: these
complement `F_1`, the space of trace tensors
(`TauCeti.isCompl_harmonicTensorsSubrep_orthogonalTraceTensors`), and the equivalence sends the
class of a tensor to its harmonic component (`Subrepresentation.quotientEquivOfIsCompl`). -/
noncomputable def quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors :
    (orthogonalTraceFiltration k n d 1).quotient.Equiv
      (harmonicTensorsSubrep k n d).toRepresentation :=
  Subrepresentation.quotientEquivOfIsCompl <| by
    rw [orthogonalTraceFiltration_one]
    exact (isCompl_harmonicTensorsSubrep_orthogonalTraceTensors k n d).symm

variable {k n d}

/-- The inverse of the equivalence sends a harmonic tensor to its class modulo `F_1`. -/
@[simp]
theorem quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors_symm_apply
    (v : (harmonicTensorsSubrep k n d).toSubmodule) :
    (quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors k n d).symm v =
      Submodule.Quotient.mk (v : ⨂[k]^d (Fin n → k)) :=
  Subrepresentation.quotientEquivOfIsCompl_symm_apply _ v

/-- The class of a harmonic tensor goes back to that tensor. -/
theorem quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors_apply_mk_of_mem
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    (quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors k n d
      (Submodule.Quotient.mk x) : ⨂[k]^d (Fin n → k)) = x := by
  have h := (quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors k n d).apply_symm_apply
    ⟨x, by rwa [harmonicTensorsSubrep_toSubmodule]⟩
  rw [quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors_symm_apply] at h
  exact congrArg Subtype.val h

/-- A tensor differs from the harmonic tensor its class corresponds to by an element of `F_1`, a
sum of trace tensors. -/
theorem sub_quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors_apply_mk_mem
    (x : ⨂[k]^d (Fin n → k)) :
    x - (quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors k n d
      (Submodule.Quotient.mk x) : ⨂[k]^d (Fin n → k)) ∈ orthogonalTraceFiltration k n d 1 :=
  Subrepresentation.sub_quotientEquivOfIsCompl_apply_mk_mem _ x

end StarOrderedField

-- On two strands `F_1` is the trace line spanned by the invariant form, a line for `n ≠ 0`, and
-- `F_2 = 0`; on one strand already `F_1 = 0`, since a single strand carries no cap.
example : orthogonalTraceFiltration ℚ 3 2 1 = orthogonalTraceLine ℚ 3 := by
  rw [orthogonalTraceFiltration_one, orthogonalTraceTensors_two]

example : Module.finrank ℚ (orthogonalTraceFiltration ℚ 3 2 1).toSubmodule = 1 := by
  rw [orthogonalTraceFiltration_one, orthogonalTraceTensors_two]
  exact finrank_orthogonalTraceLine ℚ 3

example : orthogonalTraceFiltration ℚ 3 2 2 = ⊥ :=
  orthogonalTraceFiltration_eq_bot ℚ 3 2 (by norm_num)

example : orthogonalTraceFiltration ℚ 3 1 1 = ⊥ :=
  orthogonalTraceFiltration_eq_bot ℚ 3 1 (by norm_num)

-- On two strands the top graded piece `V^{⊗2} / F_1` is the harmonic tensor square, of dimension
-- `3 ^ 2 - 1 = 8` for `n = 3`.
example : Module.finrank ℚ
    (⨂[ℚ]^2 (Fin 3 → ℚ) ⧸ (orthogonalTraceFiltration ℚ 3 2 1).toSubmodule) = 8 := by
  rw [LinearEquiv.finrank_eq
      (quotientOrthogonalTraceFiltrationOneEquivHarmonicTensors ℚ 3 2).toLinearEquiv,
    harmonicTensorsSubrep_toSubmodule]
  have h := finrank_harmonicTensors_two ℚ 3
  omega

end TauCeti
