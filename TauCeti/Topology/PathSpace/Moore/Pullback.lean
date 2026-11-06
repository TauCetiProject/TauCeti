/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.PathSpace.Moore.Between.Equiv
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.From
public import Mathlib.Analysis.Convex.Star

/-!
# Trivializing pullbacks of the based path fibration

For a map `χ : D → X` and a point `a : X`, the pullback of the end point map `P_a X → X` of the
Moore paths starting at `a` along `χ` is the space of pairs `(v, γ)` of a parameter `v` and a Moore
path `γ` from `a` to `χ v` (`TauCeti.MoorePathFrom.Pullback χ a`). The Moore loops at `a` act on
it from the left by concatenation in front, fibrewise over `D`.

A continuous family `τ` of Moore paths from `a` to `χ v`, that is a section of this pullback over
`D`, trivializes it up to homotopy: `(ω, v) ↦ (v, ω ⋆ τ_v)` is a fibre homotopy equivalence over
`D` from `Ω_a X × D` to the pullback, with homotopy inverse `(v, γ) ↦ (γ ⋆ τ_v⁻¹, v)`
(`TauCeti.MoorePathFrom.Pullback.fiberHomotopyEquivOfSection`). Both maps commute strictly with
the left action of the Moore loops at `a`, and so does every stage of the two homotopies, which
grow retracing loops of `τ_v` as in `TauCeti.MoorePathBetween.appendHomotopyEquiv`. A reversed
path is only an inverse up to homotopy, so the two maps are not mutually inverse homeomorphisms.

When `D` is a star-convex subset `S` of a real topological vector space, with centre `c`, such a
section is given by a Moore path `δ` from `a` to `χ c` followed by the images under `χ` of the
segments from `c` to the points of `S` (`TauCeti.MoorePathFrom.Pullback.radialSection`). This
applies to the characteristic map of a cell of a CW complex, whose domain is a disk. Over a cell,
the pulled-back path fibration is thus left-loop-equivariantly homotopy equivalent to the product
of the Moore loops with the disk: this is the topological input for comparing chains on the based
path space with free left modules over the chains of the Moore loops, as in Brown's construction
of twisted tensor products. When `D` is a point, the fibre homotopy equivalence is, up to the
evident identifications, `TauCeti.MoorePathBetween.loopAppendHomotopyEquiv` for the single path.

## Main definitions

* `TauCeti.MoorePathFrom.Pullback χ a`: the pullback of the based path fibration along `χ`.
* `TauCeti.MoorePathFrom.Pullback.proj`: its projection to the parameter space.
* `TauCeti.MoorePathFrom.Pullback.appendSection`: the trivializing map `Ω_a X × D → Pullback χ a`.
* `TauCeti.MoorePathFrom.Pullback.appendSymmSection`: its homotopy inverse.
* `TauCeti.MoorePathFrom.Pullback.fiberHomotopyEquivOfSection`: the fibre homotopy equivalence.
* `TauCeti.MoorePathFrom.Pullback.radialSection`: the radial section over a star-convex set.
* `TauCeti.MoorePathFrom.Pullback.radialFiberHomotopyEquiv`: the resulting trivialization over a
  star-convex set.

## Main results

* `TauCeti.MoorePathFrom.Pullback.appendSection_mul`,
  `TauCeti.MoorePathFrom.Pullback.appendSymmSection_smul`: the maps are left-loop-equivariant.
* `TauCeti.MoorePathFrom.Pullback.loopHomotopy_mul`,
  `TauCeti.MoorePathFrom.Pullback.pullbackHomotopy_smul`: so are the homotopies.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal
open unitInterval ContinuousMap

namespace TauCeti

namespace MoorePathFrom

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] {a : X}

/-- The **pullback of the based path fibration** `P_a X → X` along `χ : D → X`: the pairs `(v, γ)`
of a parameter `v` and a Moore path `γ` from `a` ending at `χ v`, with the subspace topology. -/
abbrev Pullback (χ : C(D, X)) (a : X) :=
  {x : D × MoorePathFrom X a // χ x.1 = x.2.toMoorePath.target}

namespace Pullback

variable {χ : C(D, X)}

/-- The end point of the path of a point of the pullback is the image of its parameter. -/
theorem target_eq (x : Pullback χ a) : x.1.2.toMoorePath.target = χ x.1.1 :=
  x.2.symm

/-- The projection of the pullback to the parameter space. -/
def proj (χ : C(D, X)) (a : X) : C(Pullback χ a, D) :=
  ⟨fun x ↦ x.1.1, by fun_prop⟩

@[simp]
theorem proj_apply (x : Pullback χ a) : proj χ a x = x.1.1 :=
  (rfl)

/-! ### The left action of Moore loops -/

/-- Concatenate a Moore loop at `a` in front of the path of a point of the pullback. -/
def leftAct (ω : MooreLoopSpace X a) (x : Pullback χ a) : Pullback χ a :=
  ⟨(x.1.1, ω • x.1.2), by simp [x.target_eq]⟩

@[simp]
theorem val_leftAct (ω : MooreLoopSpace X a) (x : Pullback χ a) :
    (leftAct ω x).1 = (x.1.1, ω • x.1.2) :=
  (rfl)

/-- The left loop action is jointly continuous. -/
theorem continuous_leftAct :
    Continuous fun p : MooreLoopSpace X a × Pullback χ a ↦ leftAct p.1 p.2 :=
  (continuous_snd.subtype_val.fst.prodMk (MoorePathFrom.continuous_leftAct.comp
    (continuous_fst.prodMk continuous_snd.subtype_val.snd))).subtype_mk _

@[simp]
theorem leftAct_one (x : Pullback χ a) : leftAct 1 x = x :=
  Subtype.ext (by simp)

@[simp]
theorem leftAct_mul (ω ω' : MooreLoopSpace X a) (x : Pullback χ a) :
    leftAct (ω * ω') x = leftAct ω (leftAct ω' x) :=
  Subtype.ext (by simp [mul_smul])

/-- The Moore loops at `a` act on the pullback by concatenation in front of the path, fibrewise
over the parameter space. -/
instance : MulAction (MooreLoopSpace X a) (Pullback χ a) where
  smul := leftAct
  one_smul := leftAct_one
  mul_smul := leftAct_mul

@[simp]
theorem smul_eq_leftAct (ω : MooreLoopSpace X a) (x : Pullback χ a) : ω • x = leftAct ω x :=
  (rfl)

/-- The loop action preserves the parameter. -/
theorem proj_smul (ω : MooreLoopSpace X a) (x : Pullback χ a) :
    proj χ a (ω • x) = proj χ a x :=
  (rfl)

instance : ContinuousSMul (MooreLoopSpace X a) (Pullback χ a) :=
  ⟨continuous_leftAct⟩

/-! ### The trivialization given by a section -/

variable (τ : C(D, MoorePathFrom X a)) (hτ : ∀ v, χ v = (τ v).toMoorePath.target)

include τ hτ in
/-- The path `τ v` of a section, with its specified end points. -/
def sectionPath (v : D) : MoorePathBetween X a (χ v) :=
  ⟨(τ v).toMoorePath, (τ v).source, (hτ v).symm⟩

@[simp]
theorem toMoorePath_sectionPath (v : D) :
    (sectionPath τ hτ v).toMoorePath = (τ v).toMoorePath :=
  MoorePathBetween.toMoorePath_mk _ _

include τ hτ in
/-- The **trivializing map** of a section `τ`: a loop `ω` at `a` and a parameter `v` go to the
path `ω ⋆ τ_v`. -/
def appendSection : C(MooreLoopSpace X a × D, Pullback χ a) where
  toFun p := ⟨(p.2, p.1 • τ p.2), by simp [hτ]⟩
  continuous_toFun := by fun_prop

@[simp]
theorem val_appendSection (p : MooreLoopSpace X a × D) :
    (appendSection τ hτ p).1 = (p.2, p.1 • τ p.2) :=
  (rfl)

/-- The trivializing map lies over the parameter space. -/
theorem proj_appendSection (p : MooreLoopSpace X a × D) :
    proj χ a (appendSection τ hτ p) = p.2 :=
  (rfl)

/-- The trivializing map commutes with the left action of the Moore loops. -/
theorem appendSection_mul (η ω : MooreLoopSpace X a) (v : D) :
    appendSection τ hτ (η * ω, v) = η • appendSection τ hτ (ω, v) :=
  Subtype.ext (by simp [mul_smul])

include τ hτ in
/-- The **homotopy inverse** of the trivializing map: a path `γ` from `a` to `χ v` goes to the
loop `γ ⋆ τ_v⁻¹` and the parameter `v`. -/
def appendSymmSection : C(Pullback χ a, MooreLoopSpace X a × D) :=
  ⟨fun x ↦ (⟨x.1.2.toMoorePath.trans (τ x.1.1).toMoorePath.symm (by simp [x.target_eq, hτ]),
      by simp, by simp⟩, x.1.1), by
    refine Continuous.prodMk ?_ (by fun_prop)
    refine MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
    exact (continuous_toMoorePath.comp (continuous_subtype_val.snd)).moorePath_trans
      (continuous_toMoorePath.comp (τ.continuous.comp continuous_subtype_val.fst)).moorePath_symm
      _⟩

@[simp]
theorem toMoorePath_fst_appendSymmSection (x : Pullback χ a) :
    (appendSymmSection τ hτ x).1.toMoorePath =
      x.1.2.toMoorePath.trans (τ x.1.1).toMoorePath.symm (by simp [x.target_eq, hτ]) :=
  (rfl)

/-- The homotopy inverse lies over the parameter space. -/
@[simp]
theorem snd_appendSymmSection (x : Pullback χ a) : (appendSymmSection τ hτ x).2 = x.1.1 :=
  (rfl)

/-- The homotopy inverse commutes with the left action of the Moore loops. -/
theorem appendSymmSection_smul (η : MooreLoopSpace X a) (x : Pullback χ a) :
    appendSymmSection τ hτ (η • x) =
      (η * (appendSymmSection τ hτ x).1, (appendSymmSection τ hτ x).2) :=
  Prod.ext (MooreLoopSpace.ext (by simpa using MoorePath.trans_assoc _ _ _ _ _)) rfl

/-- The retracing loops of the section depend continuously on the time and the parameter. -/
private theorem continuous_retrace_sectionPath :
    Continuous fun p : I × D ↦
      (sectionPath τ hτ p.2).retrace (toNNReal p.1 * (τ p.2).toMoorePath.length) := by
  refine MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
  simp only [Function.comp_def, MoorePathBetween.toMoorePath_retrace, toMoorePath_sectionPath]
  have h := ((continuous_toMoorePath.comp (τ.continuous.comp continuous_snd)).moorePath_truncate
    ((toNNReal_continuous.comp continuous_fst).mul
      (MoorePath.continuous_length.comp
        (continuous_toMoorePath.comp (τ.continuous.comp continuous_snd)))))
  exact h.moorePath_trans h.moorePath_symm _

/-- The homotopy from the identity of `Ω_a X × D` to `appendSymmSection ∘ appendSection`, through
maps over `D`: at time `s` a loop `ω` is followed by the retracing loop of `τ_v` up to `s` times its
duration. -/
def loopHomotopy :
    HomotopyWith (.id (MooreLoopSpace X a × D))
      ((appendSymmSection τ hτ).comp (appendSection τ hτ))
      fun f ↦ (ContinuousMap.snd : C(MooreLoopSpace X a × D, D)).comp f = .snd where
  toFun p := (p.2.1 * (sectionPath τ hτ p.2.2).retrace
    (toNNReal p.1 * (τ p.2.2).toMoorePath.length), p.2.2)
  continuous_toFun := by
    have h : Continuous fun p : I × (MooreLoopSpace X a × D) ↦
        (sectionPath τ hτ p.2.2).retrace (toNNReal p.1 * (τ p.2.2).toMoorePath.length) :=
      (continuous_retrace_sectionPath τ hτ).comp (continuous_fst.prodMk continuous_snd.snd)
    exact (continuous_snd.fst.mul h).prodMk continuous_snd.snd
  map_zero_left p := by simp
  map_one_left p := by
    have hfull : (τ p.2).toMoorePath.truncate (τ p.2).toMoorePath.length = (τ p.2).toMoorePath :=
      MoorePath.truncate_length _
    refine Prod.ext (MooreLoopSpace.ext ?_) rfl
    simp [hfull, MoorePath.trans_assoc]
  prop' s := ContinuousMap.ext fun p ↦ (rfl)

@[simp]
theorem loopHomotopy_apply (s : I) (p : MooreLoopSpace X a × D) :
    loopHomotopy τ hτ (s, p) =
      (p.1 * (sectionPath τ hτ p.2).retrace (toNNReal s * (τ p.2).toMoorePath.length), p.2) :=
  (rfl)

/-- Every stage of `loopHomotopy` commutes with left multiplication by Moore loops. -/
theorem loopHomotopy_mul (s : I) (η ω : MooreLoopSpace X a) (v : D) :
    loopHomotopy τ hτ (s, (η * ω, v)) =
      ((η * (loopHomotopy τ hτ (s, (ω, v))).1), (loopHomotopy τ hτ (s, (ω, v))).2) := by
  simp [mul_assoc]

/-- The retracing loops of the reversed section depend continuously on the time and the
parameter. -/
private theorem continuous_retrace_symm_sectionPath :
    Continuous fun p : I × D ↦
      ((sectionPath τ hτ p.2).symm.retrace
        (toNNReal p.1 * (τ p.2).toMoorePath.length)).toMoorePath := by
  simp only [MoorePathBetween.toMoorePath_retrace, MoorePathBetween.toMoorePath_symm,
    toMoorePath_sectionPath]
  have h := (continuous_toMoorePath.comp (τ.continuous.comp continuous_snd)).moorePath_symm
    |>.moorePath_truncate ((toNNReal_continuous.comp continuous_fst).mul
      (MoorePath.continuous_length.comp
        (continuous_toMoorePath.comp (τ.continuous.comp continuous_snd))))
  exact h.moorePath_trans h.moorePath_symm _

/-- The homotopy from the identity of the pullback to `appendSection ∘ appendSymmSection`, through
maps over `D`: at time `s` a path `γ` from `a` to `χ v` is followed by the retracing loop at
`χ v` of the reversal of `τ_v`, up to `s` times its duration. -/
def pullbackHomotopy :
    HomotopyWith (.id (Pullback χ a)) ((appendSection τ hτ).comp (appendSymmSection τ hτ))
      fun f ↦ (proj χ a).comp f = proj χ a where
  toFun p := ⟨(p.2.1.1, ⟨p.2.1.2.toMoorePath.trans ((sectionPath τ hτ p.2.1.1).symm.retrace
      (toNNReal p.1 * (τ p.2.1.1).toMoorePath.length)).toMoorePath (by simp [p.2.target_eq, hτ]),
      by simp⟩), by simp [hτ]⟩
  continuous_toFun := by
    have h : Continuous fun p : I × Pullback χ a ↦
        ((sectionPath τ hτ p.2.1.1).symm.retrace
          (toNNReal p.1 * (τ p.2.1.1).toMoorePath.length)).toMoorePath :=
      (continuous_retrace_symm_sectionPath τ hτ).comp
        (continuous_fst.prodMk continuous_snd.subtype_val.fst)
    refine (continuous_snd.subtype_val.fst.prodMk (Continuous.subtype_mk ?_ _)).subtype_mk _
    exact (continuous_toMoorePath.comp continuous_snd.subtype_val.snd).moorePath_trans h _
  map_zero_left x := Subtype.ext (Prod.ext rfl (MoorePathFrom.ext (by simp)))
  map_one_left x := by
    have hfull : (τ x.1.1).toMoorePath.symm.truncate (τ x.1.1).toMoorePath.length =
        (τ x.1.1).toMoorePath.symm := by
      simpa only [MoorePath.length_symm] using (τ x.1.1).toMoorePath.symm.truncate_length
    refine Subtype.ext (Prod.ext rfl (MoorePathFrom.ext ?_))
    simp [hfull, MoorePath.trans_assoc]
  prop' s := ContinuousMap.ext fun x ↦ (rfl)

@[simp]
theorem toMoorePath_snd_val_pullbackHomotopy (s : I) (x : Pullback χ a) :
    (pullbackHomotopy τ hτ (s, x)).1.2.toMoorePath =
      x.1.2.toMoorePath.trans ((sectionPath τ hτ x.1.1).symm.retrace
        (toNNReal s * (τ x.1.1).toMoorePath.length)).toMoorePath (by simp [x.target_eq, hτ]) :=
  MoorePathFrom.toMoorePath_mk _ _

/-- The homotopy `pullbackHomotopy` keeps the parameter fixed. -/
@[simp]
theorem fst_val_pullbackHomotopy (s : I) (x : Pullback χ a) :
    (pullbackHomotopy τ hτ (s, x)).1.1 = x.1.1 :=
  (rfl)

/-- Every stage of `pullbackHomotopy` commutes with the left action of the Moore loops. -/
theorem pullbackHomotopy_smul (s : I) (η : MooreLoopSpace X a) (x : Pullback χ a) :
    pullbackHomotopy τ hτ (s, η • x) = η • pullbackHomotopy τ hτ (s, x) :=
  Subtype.ext (Prod.ext rfl (MoorePathFrom.ext (by simpa using MoorePath.trans_assoc _ _ _ _ _)))

include τ hτ in
/-- **A section trivializes the pulled-back based path fibration up to homotopy.** For a
continuous family `τ` of Moore paths from `a` to `χ v`, appending `τ_v` to loops at `a` is a fibre
homotopy equivalence over `D` from `Ω_a X × D` to the pullback of `P_a X → X` along `χ`. The maps
and homotopies commute with the left action of the Moore loops (`appendSection_mul`,
`appendSymmSection_smul`, `loopHomotopy_mul` and `pullbackHomotopy_smul`). -/
def fiberHomotopyEquivOfSection :
    FiberHomotopyEquiv (ContinuousMap.snd : C(MooreLoopSpace X a × D, D)) (proj χ a) where
  toFun := appendSection τ hτ
  invFun := appendSymmSection τ hτ
  comp_toFun := (rfl)
  comp_invFun := (rfl)
  left_inv := ⟨(loopHomotopy τ hτ).symm⟩
  right_inv := ⟨(pullbackHomotopy τ hτ).symm⟩

@[simp]
theorem fiberHomotopyEquivOfSection_toFun :
    (fiberHomotopyEquivOfSection τ hτ).toFun = appendSection τ hτ :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivOfSection_invFun :
    (fiberHomotopyEquivOfSection τ hτ).invFun = appendSymmSection τ hτ :=
  (rfl)

/-! ### The radial section over a star-convex set -/

section StarConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {S : Set E} {c : S}

/-- The point `(1 - s) • c + s • v` of a set star-convex at `c`, for `v` in the set and
`s ∈ [0, 1]`. -/
private def segmentMap (hS : StarConvex ℝ (c : E) S) : C(S × I, S) :=
  ⟨fun p ↦ ⟨(1 - (p.2 : ℝ)) • (c : E) + (p.2 : ℝ) • (p.1 : E),
    hS p.1.2 (sub_nonneg.2 p.2.2.2) p.2.2.1 (sub_add_cancel _ _)⟩, by fun_prop⟩

private theorem segmentMap_zero (hS : StarConvex ℝ (c : E) S) (v : S) :
    segmentMap hS (v, 0) = c :=
  Subtype.ext (by simp [segmentMap])

private theorem segmentMap_one (hS : StarConvex ℝ (c : E) S) (v : S) :
    segmentMap hS (v, 1) = v :=
  Subtype.ext (by simp [segmentMap])

variable (χ : C(S, X)) (hS : StarConvex ℝ (c : E) S) (δ : MoorePathBetween X a (χ c))

/-- The **radial section** over a set `S` star-convex at `c`: the Moore path `δ` from `a` to `χ c`,
followed by the image under `χ` of the segment from `c` to `v`, traversed in time one. -/
def radialSection : C(S, MoorePathFrom X a) :=
  ⟨fun v ↦ ⟨δ.toMoorePath.trans (MoorePath.ofUnitPath ((χ.comp (segmentMap hS)).curry v))
      (by simp [MoorePath.source_ofUnitPath, segmentMap_zero]), by simp⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.moorePath_trans
      (MoorePath.continuous_ofUnitPath.comp (χ.comp (segmentMap hS)).curry.continuous) _⟩

/-- The radial section at `v` follows `δ` and then a segment in time one. -/
@[simp]
theorem length_radialSection (v : S) :
    (radialSection χ hS δ v).toMoorePath.length = δ.toMoorePath.length + 1 := by
  simp [radialSection, MoorePath.length_ofUnitPath]

/-- Up to the duration of `δ`, the radial section follows `δ`. -/
theorem radialSection_apply_of_le (v : S) {t : ℝ≥0} (ht : t ≤ δ.toMoorePath.length) :
    (radialSection χ hS δ v).toMoorePath t = δ.toMoorePath t := by
  simp [radialSection, MoorePath.trans_apply_of_le _ _ _ ht]

/-- The radial section at `v` is a path from `a` to `χ v`. -/
theorem target_radialSection (v : S) : (radialSection χ hS δ v).toMoorePath.target = χ v := by
  simp [radialSection, MoorePath.target_ofUnitPath, segmentMap_one]

/-- The radial section at `v` first follows `δ` and then, in time one, the image under `χ` of the
segment from `c` to `v`. -/
theorem radialSection_apply_length_add (v : S) (t : ℝ≥0) (ht : t ≤ 1) :
    (radialSection χ hS δ v).toMoorePath (δ.toMoorePath.length + t) =
      χ ⟨(1 - (t : ℝ)) • (c : E) + (t : ℝ) • (v : E),
        hS v.2 (sub_nonneg.2 (by exact_mod_cast ht)) t.2 (sub_add_cancel _ _)⟩ := by
  have hp : Set.projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, t.2, by exact_mod_cast ht⟩ :=
    Set.projIcc_of_mem _ _
  simp [radialSection, MoorePath.ofUnitPath_apply, hp, segmentMap]

/-- **Over a star-convex set the pulled-back based path fibration is trivial up to homotopy.** For
`χ : S → X` and a Moore path `δ` from `a` to `χ c`, the radial section gives a left-loop-equivariant
fibre homotopy equivalence over `S` from `Ω_a X × S` to the pullback of `P_a X → X` along `χ`. -/
def radialFiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.snd : C(MooreLoopSpace X a × S, S)) (proj χ a) :=
  fiberHomotopyEquivOfSection (radialSection χ hS δ) fun v ↦
    (target_radialSection χ hS δ v).symm

@[simp]
theorem radialFiberHomotopyEquiv_toFun :
    (radialFiberHomotopyEquiv χ hS δ).toFun =
      appendSection (radialSection χ hS δ) fun v ↦ (target_radialSection χ hS δ v).symm :=
  (rfl)

@[simp]
theorem radialFiberHomotopyEquiv_invFun :
    (radialFiberHomotopyEquiv χ hS δ).invFun =
      appendSymmSection (radialSection χ hS δ) fun v ↦ (target_radialSection χ hS δ v).symm :=
  (rfl)

end StarConvex

end Pullback

end MoorePathFrom

end TauCeti
