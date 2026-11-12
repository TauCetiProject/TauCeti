/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Genus stabilization of a Heegaard region system

A *genus stabilization* of a pointed Heegaard diagram `(Σ, α, β, z)` takes the connected sum of
`Σ`, at a point of a region `r`, with the standard torus diagram `(T², α', β')` in which `α'` and
`β'` meet transversely in a single point `c`. The new surface has genus one more, there is one
new pair of attaching curves, and one new intersection point. Cutting the punctured torus along
`α'` and `β'` leaves a square with its four corners at `c`, so the region `r` becomes a region of
Euler characteristic `χ(r) - 1` with four additional corners, all at `c`, and every other region
is unchanged. Each of the two new curves consists of a single arc from `c` to itself, with the
new region on both sides.

On the incidence data `TauCeti.HeegaardRegionSystem` this is `H.stabilize r`, whose intersection
points are `Option Point`, with `none` the new point `c`, and whose regions and basepoints are
those of `H`. The region Euler characteristics `χ` become `χ - Pi.single r 1`.

The stabilization changes none of the combinatorics that the hat complex depends on. A generator
`x` of `H` gives the generator `x ∪ {c}` of `H.stabilize r`, and every generator arises this way
(`TauCeti.HeegaardRegionSystem.stabilizeGeneratorEquiv`). A domain connects `x ∪ {c}` to
`y ∪ {c}` exactly when it connects `x` to `y`, since both sides of each new arc carry the same
multiplicity, and the periodic domains are the same. The Maslov index is unchanged as well: the
Euler measure of `D` drops by `2 D(r)` (one for the Euler characteristic and one for the four new
corners) while each of the point measures at the two generators rises by `D(r)`, the multiplicity
at all four corners of `c`. Hence the domains counted by the hat differential, its coefficients,
the relative grading and the admissibility conditions all agree, and the hat differential of the
stabilization is the hat differential of `H` transported along the generator correspondence.
Stabilizing in a region containing a basepoint preserves niceness. The Euler normalization
`∑ χ(R) - #(α ∩ β) = 2 - 2g` of a closed surface of genus `g` passes to genus `g + 1`.

This is the combinatorial half of the stabilization invariance of `\widehat{HF}`: for the
holomorphic theory one must still identify the moduli spaces of the two diagrams (Ozsváth and
Szabó, Theorem 10.2), which is not formalized here. The inverse operation, destabilization, is
not treated here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.stabilize`: the genus stabilization of `H` in the region `r`.
* `TauCeti.HeegaardRegionSystem.stabilizeGeneratorEquiv`: the correspondence `x ↦ x ∪ {c}`
  between the generators of `H` and of its stabilization.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_stabilize_iff`: the domains between
  corresponding generators agree.
* `TauCeti.HeegaardRegionSystem.periodicDomains_stabilize`: the periodic domains agree.
* `TauCeti.HeegaardRegionSystem.maslovIndex_stabilize`: the Maslov indices agree.
* `TauCeti.HeegaardRegionSystem.hatDomains_stabilize` and
  `TauCeti.HeegaardRegionSystem.hatDifferential_stabilize`: the counted domains agree, and the
  hat differential of the stabilization is conjugate to that of `H`.
* `TauCeti.HeegaardRegionSystem.relativeGrading_stabilize`: the relative gradings agree.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_stabilize_iff`,
  `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_stabilize_iff` and
  `TauCeti.HeegaardRegionSystem.stronglyAdmissible_stabilize_iff`: admissibility is unchanged.
* `TauCeti.HeegaardRegionSystem.isNice_stabilize_iff`: stabilizing in a region containing a
  basepoint preserves niceness.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1 (stabilization as a Heegaard
  move) and §10 (stabilization invariance, Theorem 10.2).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830),
  for stabilizations of nice diagrams in a region containing a basepoint.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}

section Construction

/-- Extending a curve labelling by a new point on a new curve: the fibres over the old curves
are the images of the old fibres, and the fibre over the new curve is the new point. A
permutation forming one cycle on each old fibre, extended to fix the new point, forms one cycle on
each new fibre. -/
private theorem isCycleOn_optionCongr_fiber {f : Point → Fin n} {σ : Equiv.Perm Point}
    (hσ : ∀ j, σ.IsCycleOn {q | f q = j}) (i : Fin (n + 1)) :
    Equiv.Perm.IsCycleOn (Equiv.optionCongr σ)
      {p : Option Point | p.elim (Fin.last n) (fun q => (f q).castSucc) = i} := by
  induction i using Fin.lastCases with
  | last =>
    have hs : {p : Option Point | p.elim (Fin.last n) (fun q => (f q).castSucc) = Fin.last n} =
        {none} := by
      ext p
      cases p <;> simp [Fin.castSucc_ne_last]
    rw [hs, Equiv.Perm.isCycleOn_singleton]
    simp
  | cast j =>
    have hs : {p : Option Point | p.elim (Fin.last n) (fun q => (f q).castSucc) = j.castSucc} =
        some '' {q | f q = j} := by
      ext p
      cases p <;> simp [(Fin.castSucc_ne_last j).symm]
    rw [hs]
    exact (hσ j).optionCongr

variable (H : HeegaardRegionSystem n Point Region Basepoint) (r : Region)

/-- The genus stabilization of `H` in the region `r`: the connected sum, at a point of `r`, with
the torus diagram whose two curves meet once. The intersection points are `Option Point`, where
`none` is the new point `c`, the only point on the new `α`- and `β`-curves, both labelled by
`Fin.last n`. Each new curve is a single arc from `c` to itself with the region `r` on both sides,
so `r` acquires all four corners at `c`. The regions and basepoints are those of `H`; the Euler
characteristic of `r` drops by one, which callers record as `χ - Pi.single r 1`. -/
def stabilize : HeegaardRegionSystem (n + 1) (Option Point) Region Basepoint where
  pointFintype := letI := H.pointFintype; inferInstance
  alpha p := p.elim (Fin.last n) fun q => (H.alpha q).castSucc
  beta p := p.elim (Fin.last n) fun q => (H.beta q).castSucc
  alphaNext := H.alphaNext.optionCongr
  alphaNext_isCycleOn := isCycleOn_optionCongr_fiber H.alphaNext_isCycleOn
  betaNext := H.betaNext.optionCongr
  betaNext_isCycleOn := isCycleOn_optionCongr_fiber H.betaNext_isCycleOn
  alphaLeft p := p.elim r H.alphaLeft
  alphaRight p := p.elim r H.alphaRight
  betaLeft p := p.elim r H.betaLeft
  betaRight p := p.elim r H.betaRight
  regionNonempty := H.regionNonempty
  crossingCompatible p := by
    cases p with
    | none => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | some p => simpa [← Equiv.optionCongr_symm] using H.crossingCompatible p
  regionCovered s := by
    rcases H.regionCovered s with ⟨p, hp⟩ | ⟨-, hs⟩
    · exact Or.inl ⟨some p, hp⟩
    · exact Or.inl ⟨none, Or.inl (Subsingleton.elim r s)⟩
  basepoint := H.basepoint

/-- The new intersection point lies on the new `α`-curve. -/
@[simp]
theorem stabilize_alpha_none : (H.stabilize r).alpha none = Fin.last n :=
  (rfl)

/-- The old intersection points keep their `α`-curves. -/
@[simp]
theorem stabilize_alpha_some (p : Point) : (H.stabilize r).alpha (some p) = (H.alpha p).castSucc :=
  (rfl)

/-- The new intersection point lies on the new `β`-curve. -/
@[simp]
theorem stabilize_beta_none : (H.stabilize r).beta none = Fin.last n :=
  (rfl)

/-- The old intersection points keep their `β`-curves. -/
@[simp]
theorem stabilize_beta_some (p : Point) : (H.stabilize r).beta (some p) = (H.beta p).castSucc :=
  (rfl)

/-- The successor along the `α`-curves fixes the new point and is unchanged on the old ones. -/
theorem stabilize_alphaNext : (H.stabilize r).alphaNext = H.alphaNext.optionCongr :=
  (rfl)

@[simp]
theorem stabilize_alphaNext_none : (H.stabilize r).alphaNext none = none :=
  (rfl)

@[simp]
theorem stabilize_alphaNext_some (p : Point) :
    (H.stabilize r).alphaNext (some p) = some (H.alphaNext p) :=
  (rfl)

@[simp]
theorem stabilize_alphaNext_symm_none : (H.stabilize r).alphaNext.symm none = none :=
  (rfl)

@[simp]
theorem stabilize_alphaNext_symm_some (p : Point) :
    (H.stabilize r).alphaNext.symm (some p) = some (H.alphaNext.symm p) :=
  (rfl)

/-- The successor along the `β`-curves fixes the new point and is unchanged on the old ones. -/
theorem stabilize_betaNext : (H.stabilize r).betaNext = H.betaNext.optionCongr :=
  (rfl)

@[simp]
theorem stabilize_betaNext_none : (H.stabilize r).betaNext none = none :=
  (rfl)

@[simp]
theorem stabilize_betaNext_some (p : Point) :
    (H.stabilize r).betaNext (some p) = some (H.betaNext p) :=
  (rfl)

@[simp]
theorem stabilize_betaNext_symm_none : (H.stabilize r).betaNext.symm none = none :=
  (rfl)

@[simp]
theorem stabilize_betaNext_symm_some (p : Point) :
    (H.stabilize r).betaNext.symm (some p) = some (H.betaNext.symm p) :=
  (rfl)

/-- The new `α`-arc has the region `r` on its left. -/
@[simp]
theorem stabilize_alphaLeft_none : (H.stabilize r).alphaLeft none = r :=
  (rfl)

@[simp]
theorem stabilize_alphaLeft_some (p : Point) : (H.stabilize r).alphaLeft (some p) = H.alphaLeft p :=
  (rfl)

/-- The new `α`-arc has the region `r` on its right. -/
@[simp]
theorem stabilize_alphaRight_none : (H.stabilize r).alphaRight none = r :=
  (rfl)

@[simp]
theorem stabilize_alphaRight_some (p : Point) :
    (H.stabilize r).alphaRight (some p) = H.alphaRight p :=
  (rfl)

/-- The new `β`-arc has the region `r` on its left. -/
@[simp]
theorem stabilize_betaLeft_none : (H.stabilize r).betaLeft none = r :=
  (rfl)

@[simp]
theorem stabilize_betaLeft_some (p : Point) : (H.stabilize r).betaLeft (some p) = H.betaLeft p :=
  (rfl)

/-- The new `β`-arc has the region `r` on its right. -/
@[simp]
theorem stabilize_betaRight_none : (H.stabilize r).betaRight none = r :=
  (rfl)

@[simp]
theorem stabilize_betaRight_some (p : Point) :
    (H.stabilize r).betaRight (some p) = H.betaRight p :=
  (rfl)

/-- The basepoints stay in their regions. -/
@[simp]
theorem stabilize_basepoint : (H.stabilize r).basepoint = H.basepoint :=
  (rfl)

/-- All four corners at the new point lie in the region `r`. -/
@[simp]
theorem stabilize_cornerRegion_none (i : Fin 4) : (H.stabilize r).cornerRegion none i = r := by
  fin_cases i <;> simp [cornerRegion_eq]

/-- The corners at the old points are unchanged. -/
@[simp]
theorem stabilize_cornerRegion_some (p : Point) :
    (H.stabilize r).cornerRegion (some p) = H.cornerRegion p := by
  simp [cornerRegion_eq]

end Construction

section Generator

variable {H : HeegaardRegionSystem n Point Region Basepoint} {r : Region}

/-- Every generator of the stabilization uses the new point on the new `α`-curve, the only point
there. -/
@[simp 1100]
theorem stabilize_point_last (x : (H.stabilize r).Generator) :
    (H.stabilize r).point x (Fin.last n) = none := by
  have h := (H.stabilize r).alpha_coe x (Fin.last n)
  rw [← HeegaardIntersectionSystem.point_apply] at h
  cases hx : (H.stabilize r).point x (Fin.last n) with
  | none => rfl
  | some q =>
    rw [hx, stabilize_alpha_some] at h
    exact absurd h (Fin.castSucc_ne_last _)

/-- On an old `α`-curve a generator of the stabilization uses an old point. -/
private theorem isSome_stabilize_point_castSucc (x : (H.stabilize r).Generator) (j : Fin n) :
    ((H.stabilize r).point x j.castSucc).isSome := by
  have h := (H.stabilize r).alpha_coe x j.castSucc
  rw [← HeegaardIntersectionSystem.point_apply] at h
  cases hx : (H.stabilize r).point x j.castSucc with
  | none =>
    rw [hx, stabilize_alpha_none] at h
    exact absurd h.symm (Fin.castSucc_ne_last j)
  | some q => rfl

/-- The old point of a generator of the stabilization on the old `α`-curve `j`. -/
private noncomputable def stabilizeRestrictPoint (x : (H.stabilize r).Generator) (j : Fin n) :
    Point :=
  ((H.stabilize r).point x j.castSucc).get (isSome_stabilize_point_castSucc x j)

private theorem some_stabilizeRestrictPoint (x : (H.stabilize r).Generator) (j : Fin n) :
    some (stabilizeRestrictPoint x j) = (H.stabilize r).point x j.castSucc :=
  Option.some_get _

private theorem alpha_stabilizeRestrictPoint (x : (H.stabilize r).Generator) (j : Fin n) :
    H.alpha (stabilizeRestrictPoint x j) = j := by
  have h := (H.stabilize r).alpha_coe x j.castSucc
  rw [← HeegaardIntersectionSystem.point_apply, ← some_stabilizeRestrictPoint,
    stabilize_alpha_some] at h
  exact Fin.castSucc_injective n h

private theorem bijective_beta_comp_stabilizeRestrictPoint (x : (H.stabilize r).Generator) :
    Function.Bijective (H.beta ∘ stabilizeRestrictPoint x) := by
  refine Finite.injective_iff_bijective.mp fun j k hjk => ?_
  have hβ : ∀ j, (H.beta (stabilizeRestrictPoint x j)).castSucc = x.1 j.castSucc := fun j => by
    rw [← stabilize_beta_some (r := r), some_stabilizeRestrictPoint,
      HeegaardIntersectionSystem.point_apply, HeegaardIntersectionSystem.beta_coe]
  have h : x.1 j.castSucc = x.1 k.castSucc := by
    rw [← hβ, ← hβ]
    exact congrArg Fin.castSucc hjk
  exact Fin.castSucc_injective n (x.1.injective h)

/-- The points of `x ∪ {c}`: those of `x` on the old curves and the new point on the new
`α`-curve. -/
private theorem bijective_beta_comp_snoc (x : H.Generator) :
    Function.Bijective ((H.stabilize r).beta ∘
      Fin.snoc (α := fun _ => Option Point) (fun j => some (H.point x j)) none) := by
  refine Finite.injective_iff_bijective.mp fun i k hik => ?_
  induction i using Fin.lastCases with
  | last =>
    induction k using Fin.lastCases with
    | last => rfl
    | cast k =>
      simp only [Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, stabilize_beta_none,
        stabilize_beta_some] at hik
      exact absurd hik.symm (Fin.castSucc_ne_last _)
  | cast j =>
    induction k using Fin.lastCases with
    | last =>
      simp only [Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, stabilize_beta_none,
        stabilize_beta_some] at hik
      exact absurd hik (Fin.castSucc_ne_last _)
    | cast k =>
      simp only [Function.comp_apply, Fin.snoc_castSucc, stabilize_beta_some,
        HeegaardIntersectionSystem.point_apply, HeegaardIntersectionSystem.beta_coe] at hik
      exact congrArg Fin.castSucc (x.1.injective (Fin.castSucc_injective n hik))

variable (H r) in
/-- The generators of the stabilization `H.stabilize r` correspond to those of `H`: a generator
`x` of `H` gives the generator `x ∪ {c}`, which uses the new point `c` on the new curves. -/
noncomputable def stabilizeGeneratorEquiv : H.Generator ≃ (H.stabilize r).Generator where
  toFun x := (H.stabilize r).generatorOfPointChoice
    (Fin.snoc (α := fun _ => Option Point) (fun j => some (H.point x j)) none)
    (fun i => by induction i using Fin.lastCases <;> simp) (bijective_beta_comp_snoc x)
  invFun x := H.generatorOfPointChoice (stabilizeRestrictPoint x) (alpha_stabilizeRestrictPoint x)
    (bijective_beta_comp_stabilizeRestrictPoint x)
  left_inv x := H.point_injective <| funext fun j => Option.some_injective _ <| by
    rw [HeegaardIntersectionSystem.point_apply,
      HeegaardIntersectionSystem.generatorOfPointChoice_val, some_stabilizeRestrictPoint,
      HeegaardIntersectionSystem.point_apply, HeegaardIntersectionSystem.generatorOfPointChoice_val,
      Fin.snoc_castSucc]
  right_inv x := (H.stabilize r).point_injective <| funext fun i => by
    rw [HeegaardIntersectionSystem.point_apply,
      HeegaardIntersectionSystem.generatorOfPointChoice_val]
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last, stabilize_point_last]
    | cast j =>
      rw [Fin.snoc_castSucc, ← some_stabilizeRestrictPoint, HeegaardIntersectionSystem.point_apply,
        HeegaardIntersectionSystem.generatorOfPointChoice_val]

/-- The generator `x ∪ {c}` uses the points of `x` on the old curves. -/
@[simp 1100]
theorem point_stabilizeGeneratorEquiv_castSucc (x : H.Generator) (j : Fin n) :
    (H.stabilize r).point (H.stabilizeGeneratorEquiv r x) j.castSucc = some (H.point x j) := by
  rw [stabilizeGeneratorEquiv, Equiv.coe_fn_mk, HeegaardIntersectionSystem.point_apply,
    HeegaardIntersectionSystem.generatorOfPointChoice_val, Fin.snoc_castSucc]

/-- The `0`-chain of `x ∪ {c}` agrees with that of `x` at the old points. -/
@[simp]
theorem generatorChain_stabilizeGeneratorEquiv_some (x : H.Generator) (q : Point) :
    (H.stabilize r).generatorChain (H.stabilizeGeneratorEquiv r x) (some q) =
      H.generatorChain x q := by
  classical
  rw [HeegaardIntersectionSystem.generatorChain_apply,
    HeegaardIntersectionSystem.generatorChain_apply, stabilize_alpha_some,
    point_stabilizeGeneratorEquiv_castSucc]
  simp only [Option.some_inj]

/-- The `0`-chain of `x ∪ {c}` contains the new point. -/
@[simp]
theorem generatorChain_stabilizeGeneratorEquiv_none (x : H.Generator) :
    (H.stabilize r).generatorChain (H.stabilizeGeneratorEquiv r x) none = 1 := by
  classical
  rw [HeegaardIntersectionSystem.generatorChain_apply, stabilize_alpha_none, stabilize_point_last]
  simp

end Generator

section Domain

variable {H : HeegaardRegionSystem n Point Region Basepoint} {r : Region}

/-- A domain connects `x ∪ {c}` to `y ∪ {c}` in the stabilization exactly when it connects `x`
to `y`. -/
theorem isDomainBetween_stabilize_iff {x y : H.Generator} {D : Region → ℤ} :
    (H.stabilize r).IsDomainBetween (H.stabilizeGeneratorEquiv r x)
      (H.stabilizeGeneratorEquiv r y) D ↔ H.IsDomainBetween x y D := by
  simp [funext_iff, Option.forall]

/-- The periodic domains of the stabilization are those of `H`. -/
@[simp]
theorem periodicDomains_stabilize : (H.stabilize r).periodicDomains = H.periodicDomains := by
  ext P
  simp [funext_iff, Option.forall]

/-- The stabilization is weakly admissible exactly when `H` is. -/
@[simp]
theorem weaklyAdmissible_stabilize_iff :
    (H.stabilize r).WeaklyAdmissible ↔ H.WeaklyAdmissible := by
  rw [weaklyAdmissible_iff, weaklyAdmissible_iff, periodicDomains_stabilize]

end Domain

section MaslovIndex

variable {H : HeegaardRegionSystem n Point Region Basepoint} {r : Region}

/-- The new point has all four corners in the region `r`, so its point measure is the
multiplicity at `r`. -/
theorem stabilize_pointMeasure_none (D : Region → ℤ) :
    (H.stabilize r).pointMeasure D none = D r := by
  simp only [pointMeasure_apply, stabilize_alphaNext_symm_none, stabilize_alphaLeft_none,
    stabilize_alphaRight_none]
  ring

/-- The point measures at the old points are unchanged. -/
theorem stabilize_pointMeasure_some (D : Region → ℤ) (p : Point) :
    (H.stabilize r).pointMeasure D (some p) = H.pointMeasure D p := by
  simp

/-- The point measure of `D` at `x ∪ {c}` is that at `x` plus the multiplicity of `D` at `r`. -/
theorem generatorPointMeasure_stabilizeGeneratorEquiv (x : H.Generator) (D : Region → ℤ) :
    (H.stabilize r).generatorPointMeasure (H.stabilizeGeneratorEquiv r x) D =
      H.generatorPointMeasure x D + D r := by
  rw [generatorPointMeasure_apply, generatorPointMeasure_apply, Fin.sum_univ_castSucc]
  simp only [point_stabilizeGeneratorEquiv_castSucc, stabilize_point_last,
    stabilize_pointMeasure_some, stabilize_pointMeasure_none]

variable [Fintype Point] [DecidableEq Region]

/-- The stabilization adds the four corners at the new point to the region `r`. -/
theorem cornerCount_stabilize (s : Region) :
    (H.stabilize r).cornerCount s = H.cornerCount s + if r = s then 4 else 0 := by
  simp only [cornerCount_eq_card, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_option,
    stabilize_cornerRegion_none, stabilize_cornerRegion_some]
  split_ifs <;> simp [add_comm]

/-- Stabilizing in a region containing a basepoint preserves niceness: the regions without
basepoints, their Euler characteristics and their corners are unchanged. -/
theorem isNice_stabilize_iff {χ : Region → ℤ} (hr : ∃ z, H.basepoint z = r) :
    (H.stabilize r).IsNice (χ - Pi.single r 1) ↔ H.IsNice χ := by
  obtain ⟨z, rfl⟩ := hr
  rw [isNice_iff, isNice_iff]
  refine forall_congr' fun s => imp_congr_right fun hs => ?_
  have hrs : H.basepoint z ≠ s := hs z
  simp [cornerCount_stabilize, hrs, hrs.symm]

variable [Fintype Region]

/-- The Euler measure of a domain in the stabilization, with the Euler characteristic of `r`
lowered by one, is that in `H` minus twice the multiplicity at `r`: one for the Euler
characteristic and one for the four new corners. -/
theorem eulerMeasure_stabilize (χ D : Region → ℤ) :
    (H.stabilize r).eulerMeasure (χ - Pi.single r 1) D = H.eulerMeasure χ D - 2 * D r := by
  simp only [eulerMeasure_eq_sub_sum_pointMeasure, Fintype.sum_option,
    stabilize_pointMeasure_none, stabilize_pointMeasure_some, Pi.sub_apply, Int.cast_sub,
    sub_mul, Finset.sum_sub_distrib]
  simp [Pi.single_apply]
  ring

/-- The stabilization preserves the Maslov index of domains between corresponding generators,
for the Euler characteristics `χ - Pi.single r 1`. -/
theorem maslovIndex_stabilize (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    (H.stabilize r).maslovIndex (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x)
      (H.stabilizeGeneratorEquiv r y) D = H.maslovIndex χ x y D := by
  simp only [maslovIndex_apply, eulerMeasure_stabilize,
    generatorPointMeasure_stabilizeGeneratorEquiv]
  ring

/-- The stabilization lowers `∑ χ(R) - #(α ∩ β)` by two, the change in the Euler characteristic
of a closed surface when its genus rises by one. -/
theorem sum_sub_single_sub_card_option (χ : Region → ℤ) :
    ∑ s, (χ - Pi.single r 1 : Region → ℤ) s - (Fintype.card (Option Point) : ℤ) =
      ∑ s, χ s - Fintype.card Point - 2 := by
  simp [Finset.sum_sub_distrib]
  ring

/-- The Euler normalization of a closed surface of genus `n` for `H` gives that of genus `n + 1`
for its stabilization. -/
theorem sum_sub_single_sub_card_option_eq {χ : Region → ℤ}
    (hχ : ∑ s, χ s - Fintype.card Point = 2 - 2 * (n : ℤ)) :
    ∑ s, (χ - Pi.single r 1 : Region → ℤ) s - (Fintype.card (Option Point) : ℤ) =
      2 - 2 * ((n + 1 : ℕ) : ℤ) := by
  rw [sum_sub_single_sub_card_option, hχ]
  push_cast
  ring

/-- The periodic Maslov indices at `x ∪ {c}` are those at `x`. -/
@[simp]
theorem periodicMaslovIndices_stabilize (χ : Region → ℤ) (x : H.Generator) :
    (H.stabilize r).periodicMaslovIndices (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x) =
      H.periodicMaslovIndices χ x := by
  ext q
  simp only [mem_periodicMaslovIndices_iff, periodicDomains_stabilize, maslovIndex_stabilize]

/-- The stabilization is weakly admissible at `x ∪ {c}` exactly when `H` is weakly admissible at
`x`. -/
@[simp]
theorem weaklyAdmissibleAt_stabilize_iff (χ : Region → ℤ) (x : H.Generator) :
    (H.stabilize r).WeaklyAdmissibleAt (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x) ↔
      H.WeaklyAdmissibleAt χ x := by
  simp only [weaklyAdmissibleAt_def, periodicDomains_stabilize, maslovIndex_stabilize]

/-- The stabilization is strongly admissible at `x ∪ {c}` exactly when `H` is strongly
admissible at `x`. -/
@[simp]
theorem stronglyAdmissible_stabilize_iff (χ : Region → ℤ) (x : H.Generator) :
    (H.stabilize r).StronglyAdmissible (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x) ↔
      H.StronglyAdmissible χ x := by
  simp only [stronglyAdmissible_iff, periodicDomains_stabilize, maslovIndex_stabilize]

/-- In a singly pointed diagram of a closed surface of genus `n` whose periodic domains have
Maslov index zero at `x`, the relative grading of `x ∪ {c}` and `y ∪ {c}` is that of `x` and
`y`. -/
theorem relativeGrading_stabilize [Subsingleton Basepoint] {χ : Region → ℤ}
    (hχ : ∑ s, χ s - Fintype.card Point = 2 - 2 * (n : ℤ)) (z : Basepoint) {x : H.Generator}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (y : H.Generator) :
    (H.stabilize r).relativeGrading (χ - Pi.single r 1) z (H.stabilizeGeneratorEquiv r x)
      (H.stabilizeGeneratorEquiv r y) = H.relativeGrading χ z x y := by
  by_cases h : ∃ D, H.IsDomainBetween x y D
  · obtain ⟨D, hD⟩ := h
    have hP' : ∀ P ∈ (H.stabilize r).periodicDomains, (H.stabilize r).maslovIndex
        (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x) (H.stabilizeGeneratorEquiv r x) P =
          0 := by
      intro P hPmem
      rw [periodicDomains_stabilize] at hPmem
      rw [maslovIndex_stabilize]
      exact hP P hPmem
    rw [(isDomainBetween_stabilize_iff.mpr hD).relativeGrading_eq z
        (sum_sub_single_sub_card_option_eq hχ) hP', hD.relativeGrading_eq z hχ hP,
      maslovIndex_stabilize, stabilize_basepoint]
  · push Not at h
    have h' : ∀ D, ¬(H.stabilize r).IsDomainBetween (H.stabilizeGeneratorEquiv r x)
        (H.stabilizeGeneratorEquiv r y) D := fun D hD => h D (isDomainBetween_stabilize_iff.mp hD)
    rw [relativeGrading_of_forall_not_isDomainBetween z h',
      relativeGrading_of_forall_not_isDomainBetween z h]

/-- The domains counted by the hat differential from `x ∪ {c}` to `y ∪ {c}` are those counted
from `x` to `y`. -/
@[simp]
theorem hatDomains_stabilize (χ : Region → ℤ) (x y : H.Generator) :
    (H.stabilize r).hatDomains (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x)
      (H.stabilizeGeneratorEquiv r y) = H.hatDomains χ x y := by
  ext D
  simp only [mem_hatDomains_iff, isDomainBetween_stabilize_iff, stabilize_basepoint,
    maslovIndex_stabilize]

/-- The hat differential coefficients of the stabilization are those of `H`. -/
@[simp]
theorem hatCoefficient_stabilize (χ : Region → ℤ) (x y : H.Generator) :
    (H.stabilize r).hatCoefficient (χ - Pi.single r 1) (H.stabilizeGeneratorEquiv r x)
      (H.stabilizeGeneratorEquiv r y) = H.hatCoefficient χ x y := by
  rw [hatCoefficient_def, hatCoefficient_def, hatDomains_stabilize]

/-- The hat differential of the stabilization is the hat differential of `H` transported along
the generator correspondence `x ↦ x ∪ {c}`. -/
theorem hatDifferential_stabilize (χ : Region → ℤ) :
    (H.stabilize r).hatDifferential (χ - Pi.single r 1) =
      (Finsupp.domLCongr (H.stabilizeGeneratorEquiv r)).conj (H.hatDifferential χ) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := (H.stabilizeGeneratorEquiv r).surjective x'
  obtain ⟨y, rfl⟩ := (H.stabilizeGeneratorEquiv r).surjective y'
  simp [LinearEquiv.conj_apply]

end MaslovIndex

end HeegaardRegionSystem

end TauCeti
