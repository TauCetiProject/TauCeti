/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.LinearAlgebra.RootSystem.Weyl.IntervalBondGcd
public import TauCeti.RepresentationTheory.LSPath.Linked
public import TauCeti.RepresentationTheory.LSPath.Realization

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Set.Nat
import TauCeti.Data.Rat.NumDenDvd
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Fixed-chain simplices of Lakshmibai–Seshadri paths

Let `λ` be a weight of a finite reduced root datum with a base, and let `τ₀, …, τ_{n-1}` be minimal
coset representatives of `W / W_λ`, typically a chain `τ₀ > ⋯ > τ_{n-1}`, that is a simplex of the
order complex of the Bruhat order on `W / W_λ` (for regular `λ` in type `A₂` this complex is
`TauCeti.symmetricThreeBruhatComplex`, with four maximal tetrahedra). A point `x` of the standard
simplex `Convexity.StdSimplex 𝕜 (Fin n)` over an ordered field `𝕜` gives the piecewise-linear path
`TauCeti.LSPath.chainSimplexPath`, which runs along the realized orbit weight `f (τ_j λ)` for the
time `x_j`. Littelmann's paths of shape `λ` are the points of these simplices with directions in a
chain and rational coordinates satisfying an integrality condition at each break.

The realization respects the simplicial structure: for a monotone map `σ : Fin m → Fin n`, a point
of the simplex of `τ ∘ σ` and its image under `σ` in the simplex of `τ` have the same path
(`TauCeti.LSPath.chainSimplexPath_map`). For face inclusions this identifies the faces of a
simplex, where some coordinates vanish, with the simplices of subchains; for degeneracies it says
that merging a repeated adjacent direction, adding up its coordinates, gives the same point.

The face data `TauCeti.LSPath.faceData` of a point lists the directions with nonzero coordinate
together with these coordinates. For dominant `λ` and a realization separating the orbit `W λ` with
no two realized orbit weights on a common ray, two points of the simplices of sequences of
distinct minimal coset representatives have the same path exactly when they have the same face
data (`TauCeti.LSPath.chainSimplexPath_eq_chainSimplexPath_iff`): the simplices are glued exactly
along their common faces.

The simplices are continua, whereas the Lakshmibai–Seshadri paths of a dominant shape are finitely
many. The Lakshmibai–Seshadri points `TauCeti.LSPath.chainLSPoints` of a simplex are the points
whose face data are the directions and durations of an LS path, equivalently, under the
hypotheses of the gluing theorem, whose path is the realized path of an LS path; for distinct
directions they are finitely many, and the rational points among them in the open simplex of a
chain are cut out by the integral break test: the break `a_{j+1} = x_0 + ⋯ + x_j` has denominator
dividing the interval bond gcd `d_λ(τ_j, τ_{j+1})`. On the edge of a chain `x > y` the interior
Lakshmibai–Seshadri points are the `d_λ(x, y) - 1` breaks `k / d_λ(x, y)`; for a bond `2` the only
one is `1 / 2`, while `1 / 3` is a point of the edge failing the test.

## Main definitions

* `TauCeti.LSPath.chainSimplexPath`: the path of a point of the simplex of a list of directions.
* `TauCeti.LSPath.faceData`: the directions with nonzero coordinate of a simplex point, with these
  coordinates.
* `TauCeti.LSPath.simplexPoint`: the point of an LS path in the simplex of its directions.
* `TauCeti.LSPath.chainLSPoints`: the Lakshmibai–Seshadri points of the simplex of a list of
  directions.

## Main results

* `TauCeti.LSPath.chainSimplexPath_map`: **the realization commutes with the face and degeneracy
  maps**.
* `TauCeti.LSPath.chainSimplexPath_eq_straight`: the simplex of one direction is a single point.
* `TauCeti.LSPath.chainSimplexPath_eq_chainSimplexPath_iff`: **chain simplices are glued exactly
  along common faces**, through their face data.
* `TauCeti.LSPath.toPLPath_eq_chainSimplexPath` and
  `TauCeti.LSPath.mem_chainLSPoints_iff_exists_toPLPath_eq`: the realized LS paths are the paths of
  the Lakshmibai–Seshadri points.
* `TauCeti.LSPath.finite_chainLSPoints`: a chain simplex has finitely many Lakshmibai–Seshadri
  points.
* `TauCeti.LSPath.mem_chainLSPoints_iff_den_dvd`: **the integral break test** for the rational
  points of the open simplex of a chain.
* `TauCeti.LSPath.mem_chainLSPoints_pair_iff` and
  `TauCeti.LSPath.ncard_interior_chainLSPoints_pair`: the interior Lakshmibai–Seshadri points of an
  edge `x > y` are the `d_λ(x, y) - 1` breaks `k / d_λ(x, y)`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

open Convexity

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N} {b : P.Base}
  {lam : M} {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}
  {m n : ℕ}

/-! ### The simplex of a list of directions -/

section Simplex

variable [IsStrictOrderedRing 𝕜]

variable (lam f) in
/-- The path of the point `x` of the simplex spanned by the directions `τ₀, …, τ_{n-1}`: it runs
along the realized orbit weight `f (τ_j λ)` for the time `x_j`, the barycentric coordinate of `x`
at the vertex `j`. -/
noncomputable def chainSimplexPath (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) :
    PLPath 𝕜 V :=
  PLPath.ofSegments 𝕜 (List.ofFn fun j ↦ x.weights j • f (τ j • lam))

theorem chainSimplexPath_def (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) :
    chainSimplexPath lam f τ x =
      PLPath.ofSegments 𝕜 (List.ofFn fun j ↦ x.weights j • f (τ j • lam)) :=
  (rfl)

/-- The endpoint of the path of a simplex point is the barycentre `∑_j x_j f (τ_j λ)` of the
realized orbit weights of the vertices. -/
@[simp]
theorem endpoint_chainSimplexPath (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) :
    (chainSimplexPath lam f τ x).endpoint = ∑ j, x.weights j • f (τ j • lam) := by
  rw [chainSimplexPath_def, PLPath.endpoint_ofSegments, List.sum_ofFn]

/-- **Simplicial functoriality.** For a monotone map `σ : Fin m → Fin n`, the point of the simplex
of `τ ∘ σ` with coordinates `x` has the path of its image under `σ` in the simplex of `τ`. For a
face inclusion `σ` this identifies the face of the simplex of `τ` with the simplex of the
subsequence `τ ∘ σ`; for a degeneracy `σ` it says that removing a repeated direction, adding up
the coordinates of its copies, gives the same point. -/
theorem chainSimplexPath_map {σ : Fin m → Fin n} (hσ : Monotone σ) (τ : Fin n → P.weylGroup)
    (x : StdSimplex 𝕜 (Fin m)) :
    chainSimplexPath lam f τ (x.map σ) = chainSimplexPath lam f (τ ∘ σ) x := by
  have h := PLPath.ofSegments_ofFn_smul_comp_of_monotone (𝕜 := 𝕜) (fun k ↦ f (τ k • lam)) hσ
    (c := fun i ↦ x.weights i) fun i ↦ x.weights_nonneg i
  rw [chainSimplexPath_def, chainSimplexPath_def]
  simp only [Function.comp_apply] at h ⊢
  rw [h]
  simp [Finsupp.mapDomain_apply, Finsupp.sum_fintype, Finsupp.single_apply]

/-- The vertex `j` of the simplex of `τ` is the straight path along `f (τ_j λ)`. -/
@[simp]
theorem chainSimplexPath_single (τ : Fin n → P.weylGroup) (j : Fin n) :
    chainSimplexPath lam f τ (StdSimplex.single (R := 𝕜) j) =
      PLPath.straight 𝕜 (f (τ j • lam)) := by
  have h := chainSimplexPath_map (lam := lam) (f := f) (σ := fun _ : Fin 1 ↦ j)
    (fun _ _ _ ↦ le_rfl) τ (StdSimplex.single (R := 𝕜) (0 : Fin 1))
  rw [StdSimplex.map_single] at h
  rw [h, chainSimplexPath_def, PLPath.straight_def]
  simp

/-- The simplex of a single direction is a single point, the straight path along it. -/
theorem chainSimplexPath_eq_straight (τ : Fin 1 → P.weylGroup) (x : StdSimplex 𝕜 (Fin 1)) :
    chainSimplexPath lam f τ x = PLPath.straight 𝕜 (f (τ 0 • lam)) := by
  rw [Subsingleton.elim x (StdSimplex.single 0), chainSimplexPath_single]

end Simplex

/-! ### Face data and gluing -/

section Gluing

/-- The **face data** of a point `x` of the simplex of `τ`: the directions `τ_j` at which `x` has a
nonzero coordinate, in order, together with these coordinates. It records the open face of the
simplex containing `x` and the position of `x` in it. -/
def faceData (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) : List (P.weylGroup × 𝕜) :=
  (List.ofFn fun j ↦ (τ j, x.weights j)).filter fun p ↦ p.2 ≠ 0

theorem faceData_def (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) :
    faceData τ x = (List.ofFn fun j ↦ (τ j, x.weights j)).filter fun p ↦ p.2 ≠ 0 :=
  (rfl)

theorem mem_faceData_iff {τ : Fin n → P.weylGroup} {x : StdSimplex 𝕜 (Fin n)}
    {p : P.weylGroup × 𝕜} :
    p ∈ faceData τ x ↔ ∃ j, x.weights j ≠ 0 ∧ (τ j, x.weights j) = p := by
  simp only [faceData_def, List.mem_filter, List.mem_ofFn, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, rfl⟩, h⟩
    exact ⟨j, h, rfl⟩
  · rintro ⟨j, h, rfl⟩
    exact ⟨⟨j, rfl⟩, h⟩

/-- The coordinates recorded in the face data are positive. -/
theorem pos_of_mem_faceData {τ : Fin n → P.weylGroup} {x : StdSimplex 𝕜 (Fin n)}
    {p : P.weylGroup × 𝕜} (hp : p ∈ faceData τ x) : 0 < p.2 := by
  obtain ⟨j, hj, rfl⟩ := mem_faceData_iff.mp hp
  exact (x.weights_nonneg j).lt_of_ne' hj

/-- A sum over the face data of a function vanishing at coordinate `0` is the sum over all the
vertices. -/
theorem sum_map_faceData {R : Type*} [AddCommMonoid R] (τ : Fin n → P.weylGroup)
    (x : StdSimplex 𝕜 (Fin n)) {g : P.weylGroup × 𝕜 → R} (hg : ∀ w, g (w, 0) = 0) :
    ((faceData τ x).map g).sum = ∑ j, g (τ j, x.weights j) := by
  rw [← List.sum_ofFn, faceData_def, show (List.ofFn fun j ↦ g (τ j, x.weights j)) =
    (List.ofFn fun j ↦ (τ j, x.weights j)).map g by simp [List.map_ofFn, Function.comp_def]]
  generalize (List.ofFn fun j ↦ (τ j, x.weights j)) = l
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨w, d⟩ := p
    by_cases hd : d = 0
    · subst hd
      rw [List.filter_cons_of_neg (by simp), List.map_cons, List.sum_cons, hg, zero_add, ih]
    · rw [List.filter_cons_of_pos (by simpa using hd), List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons, ih]

/-- The coordinates recorded in the face data add up to `1`. -/
@[simp]
theorem sum_map_snd_faceData (τ : Fin n → P.weylGroup) (x : StdSimplex 𝕜 (Fin n)) :
    ((faceData τ x).map Prod.snd).sum = 1 := by
  rw [sum_map_faceData τ x fun _ ↦ rfl, StdSimplex.total_of_fintype]

/-- For distinct directions, the face data determine the point of the simplex. -/
theorem faceData_injective {τ : Fin n → P.weylGroup} (hτ : Function.Injective τ) :
    Function.Injective (faceData (𝕜 := 𝕜) τ) := by
  classical
  intro x y h
  refine StdSimplex.ext (Finsupp.ext fun j ↦ ?_)
  have key (z : StdSimplex 𝕜 (Fin n)) :
      ((faceData τ z).map fun p ↦ if p.1 = τ j then p.2 else 0).sum = z.weights j := by
    rw [sum_map_faceData τ z fun _ ↦ by simp]
    simp [hτ.eq_iff]
  rw [← key x, ← key y, h]

/-- If a function `g` of the directions separates the directions `τ_j`, its values along the face
data are pairwise distinct. -/
private theorem nodup_map_faceData {α : Type*} {τ : Fin n → P.weylGroup} {g : P.weylGroup → α}
    (hg : Function.Injective (g ∘ τ)) (x : StdSimplex 𝕜 (Fin n)) :
    ((faceData τ x).map fun p ↦ g p.1).Nodup := by
  refine (List.filter_sublist.map _).nodup ?_
  simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.mpr hg

variable [IsStrictOrderedRing 𝕜]

variable (lam f) in
/-- The path of a simplex point is presented by its face data. -/
theorem chainSimplexPath_eq_ofSegments_faceData (τ : Fin n → P.weylGroup)
    (x : StdSimplex 𝕜 (Fin n)) :
    chainSimplexPath lam f τ x =
      PLPath.ofSegments 𝕜 ((faceData τ x).map fun p ↦ p.2 • f (p.1 • lam)) := by
  rw [faceData_def, PLPath.ofSegments_map_filter _ _ fun p _ hp ↦ by simp_all, List.map_ofFn,
    chainSimplexPath_def, Function.comp_def]

variable [Finite ι] [P.IsReduced]

omit [IsStrictOrderedRing 𝕜] in
/-- For a dominant shape and distinct minimal coset representatives `τ_j`, the timed presentation
running along the face data of a simplex point, each entry `(w, d)` traversed in time `d` with
velocity `f (w λ)`, is distinguished for the realized orbit. -/
private theorem isDistinguished_faceData (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam)) {τ : Fin n → P.weylGroup}
    (hτ : Function.Injective τ)
    (hmin : ∀ j, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ j))
    (x : StdSimplex 𝕜 (Fin n)) :
    PLPath.IsDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam))
      ((faceData τ x).map fun p ↦ (p.2, p.2 • f (p.1 • lam))) := by
  have := P.flip_isReduced
  have hslope : ∀ p ∈ faceData τ x, p.2⁻¹ • p.2 • f (p.1 • lam) = f (p.1 • lam) :=
    fun p hp ↦ inv_smul_smul₀ (pos_of_mem_faceData hp).ne' _
  refine ⟨PLPath.isTimed_iff.mpr ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact pos_of_mem_faceData hp
  · rw [PLPath.duration_def, List.map_map]
    exact sum_map_snd_faceData τ x
  · simp only [List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, (hslope p hp).symm⟩
  · have hmap : ((faceData τ x).map fun p ↦ (p.2, p.2 • f (p.1 • lam))).map
        (fun y ↦ y.1⁻¹ • y.2) = (faceData τ x).map fun p ↦ f (p.1 • lam) := by
      rw [List.map_map]
      exact List.map_congr_left fun p hp ↦ hslope p hp
    rw [hmap]
    refine List.Pairwise.isChain (nodup_map_faceData (g := fun w ↦ f (w • lam)) ?_ x)
    exact fun i j h ↦ hτ (eq_of_isMinimalCosetRep_of_smul_eq hlam (hmin i) (hmin j)
      (hf ⟨_, rfl⟩ ⟨_, rfl⟩ h))

/-- **Gluing of chain simplices.** For a dominant shape `λ` and a realization `f` injective on the
orbit `W λ` with no two realized orbit weights on a common ray, two points of the simplices of
sequences of distinct minimal coset representatives have the same path exactly when they have the
same face data: the simplices are glued exactly along common faces, through their identical
directions and coordinates. -/
theorem chainSimplexPath_eq_chainSimplexPath_iff (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    {n' : ℕ} {τ : Fin n → P.weylGroup} {τ' : Fin n' → P.weylGroup} (hτ : Function.Injective τ)
    (hτ' : Function.Injective τ')
    (hmin : ∀ j, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ j))
    (hmin' : ∀ j, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ' j))
    {x : StdSimplex 𝕜 (Fin n)} {x' : StdSimplex 𝕜 (Fin n')} :
    chainSimplexPath lam f τ x = chainSimplexPath lam f τ' x' ↔ faceData τ x = faceData τ' x' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by
    rw [chainSimplexPath_eq_ofSegments_faceData, h, ← chainSimplexPath_eq_ofSegments_faceData]⟩
  have := P.flip_isReduced
  rw [chainSimplexPath_eq_ofSegments_faceData, chainSimplexPath_eq_ofSegments_faceData] at h
  have heq := (isDistinguished_faceData hlam hf hτ hmin x).unique
    (isDistinguished_faceData hlam hf hτ' hmin' x') hS (by rw [List.map_map, List.map_map]; exact h)
  -- Entry by entry, the timed entry `(d, d • f (w λ))` recovers `d > 0`, then `f (w λ)`, then the
  -- minimal coset representative `w`.
  have hlen : (faceData τ x).length = (faceData τ' x').length := by
    simpa using congrArg List.length heq
  refine List.ext_getElem hlen fun k hk hk' ↦ ?_
  have hentry := List.getElem_of_eq heq (by simpa using hk)
  simp only [List.getElem_map, Prod.mk.injEq] at hentry
  obtain ⟨hd, hv⟩ := hentry
  obtain ⟨i, -, hi⟩ := mem_faceData_iff.mp (List.getElem_mem hk)
  obtain ⟨i', -, hi'⟩ := mem_faceData_iff.mp (List.getElem_mem hk')
  have hpos := pos_of_mem_faceData (List.getElem_mem hk)
  rw [← hd] at hv
  refine Prod.ext ?_ hd
  rw [← hi, ← hi'] at hv ⊢
  exact eq_of_isMinimalCosetRep_of_smul_eq hlam (hmin i) (hmin' i')
    (hf ⟨_, rfl⟩ ⟨_, rfl⟩ (smul_right_injective V (hi ▸ hpos).ne' hv))

end Gluing

/-! ### Lakshmibai–Seshadri points -/

section LSPoints

variable [IsStrictOrderedRing 𝕜] [Finite ι] [P.IsReduced]

variable (𝕜) in
/-- The point of the simplex of the directions of an LS path whose coordinates are the durations
`a_{j+1} - a_j` of its segments. -/
noncomputable def simplexPoint (π : LSPath P b lam) : StdSimplex 𝕜 (Fin (π.length + 1)) where
  weights := Finsupp.equivFunOnFinite.symm fun j ↦ (π.duration j : 𝕜)
  nonneg := Finsupp.le_def.mpr fun j ↦ by simpa using (π.duration_pos j).le
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    simp [← Rat.cast_sum]

@[simp]
theorem weights_simplexPoint (π : LSPath P b lam) (j : Fin (π.length + 1)) :
    (π.simplexPoint 𝕜).weights j = π.duration j := by
  simp [simplexPoint]

/-- The path of an LS path is the path of its point in the simplex of its directions. -/
theorem toPLPath_eq_chainSimplexPath (π : LSPath P b lam) :
    π.toPLPath 𝕜 f = chainSimplexPath lam f (fun j ↦ (π.dir j).val) (π.simplexPoint 𝕜) := by
  simp [toPLPath_def, timed_def, chainSimplexPath_def, List.map_ofFn, Function.comp_def]

/-- The face data of the point of an LS path are its directions and durations. -/
@[simp]
theorem faceData_simplexPoint (π : LSPath P b lam) :
    faceData (fun j ↦ (π.dir j).val) (π.simplexPoint 𝕜) =
      π.dirDurations.map fun p ↦ (p.1, (p.2 : 𝕜)) := by
  rw [faceData_def, List.filter_eq_self.mpr fun p hp ↦ ?_]
  · exact List.ext_getElem (by simp) fun k _ _ ↦ by
      simp only [List.getElem_ofFn, List.getElem_map, getElem_dirDurations, weights_simplexPoint]
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    simpa using (π.duration_pos j).ne'

variable (b lam) in
/-- The **Lakshmibai–Seshadri points** of the simplex of a list of directions `τ`: the points whose
face data are the directions and durations of an LS path of shape `λ`. For a dominant shape, a
realization injective on the orbit with no two realized orbit weights on a common ray, and distinct
minimal coset representatives, they are the points whose path is the realized path of an LS path
(`TauCeti.LSPath.mem_chainLSPoints_iff_exists_toPLPath_eq`); for a dominant shape and distinct
directions there are finitely many (`TauCeti.LSPath.finite_chainLSPoints`), and for rational points
of the open simplex of a chain they are cut out by the integrality of the breaks
(`TauCeti.LSPath.mem_chainLSPoints_iff_den_dvd`). -/
def chainLSPoints (τ : Fin n → P.weylGroup) : Set (StdSimplex 𝕜 (Fin n)) :=
  {x | ∃ π : LSPath P b lam, faceData τ x = π.dirDurations.map fun p ↦ (p.1, (p.2 : 𝕜))}

omit [IsStrictOrderedRing 𝕜] in
theorem mem_chainLSPoints_iff {τ : Fin n → P.weylGroup} {x : StdSimplex 𝕜 (Fin n)} :
    x ∈ chainLSPoints b lam τ ↔
      ∃ π : LSPath P b lam, faceData τ x = π.dirDurations.map fun p ↦ (p.1, (p.2 : 𝕜)) :=
  Iff.rfl

/-- The point of an LS path is a Lakshmibai–Seshadri point of the simplex of its directions. -/
theorem simplexPoint_mem_chainLSPoints (π : LSPath P b lam) :
    π.simplexPoint 𝕜 ∈ chainLSPoints b lam fun j ↦ (π.dir j).val :=
  ⟨π, faceData_simplexPoint π⟩

/-- For a dominant shape, a realization injective on the orbit with no two realized orbit weights
on a common ray, and distinct minimal coset representatives `τ_j`, the Lakshmibai–Seshadri points
of the simplex of `τ` are exactly the points whose path is the realized path of an LS path. -/
theorem mem_chainLSPoints_iff_exists_toPLPath_eq (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    {τ : Fin n → P.weylGroup} (hτ : Function.Injective τ)
    (hmin : ∀ j, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ j))
    {x : StdSimplex 𝕜 (Fin n)} :
    x ∈ chainLSPoints b lam τ ↔
      ∃ π : LSPath P b lam, π.toPLPath 𝕜 f = chainSimplexPath lam f τ x := by
  refine exists_congr fun π ↦ ?_
  rw [toPLPath_eq_chainSimplexPath, chainSimplexPath_eq_chainSimplexPath_iff hlam hf hS
    (fun i j h ↦ π.dir_injective (Subtype.ext h)) hτ (fun j ↦ (π.dir j).property) hmin,
    faceData_simplexPoint, eq_comm]

omit [IsStrictOrderedRing 𝕜] in
/-- **The Lakshmibai–Seshadri points of a chain simplex are finite in number**, for a dominant
shape and distinct directions, whereas the simplex itself is infinite as soon as it has two
vertices. -/
theorem finite_chainLSPoints (hlam : lam ∈ dominantChamber P b) {τ : Fin n → P.weylGroup}
    (hτ : Function.Injective τ) : (chainLSPoints b lam τ : Set (StdSimplex 𝕜 (Fin n))).Finite := by
  have := finite hlam
  refine Set.Finite.of_finite_image ((Set.finite_range fun π : LSPath P b lam ↦
    π.dirDurations.map fun p ↦ (p.1, (p.2 : 𝕜))).subset ?_) (faceData_injective hτ).injOn
  rintro _ ⟨x, ⟨π, hπ⟩, rfl⟩
  exact ⟨π, hπ.symm⟩

/-- **The integral break test.** For a dominant shape and a chain `τ₀ > τ₁ > ⋯ > τ_s` of minimal
coset representatives, a rational point of the open simplex of the chain is a
Lakshmibai–Seshadri point exactly when each internal break `a_{j+1} = x_0 + ⋯ + x_j` has
denominator dividing the interval bond gcd `d_λ(τ_j, τ_{j+1})`. -/
theorem mem_chainLSPoints_iff_den_dvd (hlam : lam ∈ dominantChamber P b) {s : ℕ}
    {τ : Fin (s + 1) → P.weylGroup}
    (hmin : ∀ j, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ j))
    (hle : ∀ j : Fin s, (weylCoxeterSystem P b).BruhatLE (τ j.succ) (τ j.castSucc))
    (hne : ∀ j : Fin s, τ j.succ ≠ τ j.castSucc) {x : StdSimplex ℚ (Fin (s + 1))}
    (hx : ∀ j, x.weights j ≠ 0) :
    x ∈ chainLSPoints b lam τ ↔ ∀ j : Fin s,
      (∑ k ∈ Finset.Iic j.castSucc, x.weights k).den ∣
        intervalBondGcd b lam (τ j.castSucc) (τ j.succ) := by
  set L := List.ofFn fun j ↦ (τ j, x.weights j) with hLdef
  have hL : faceData τ x = L := List.filter_eq_self.mpr <| by simp [List.mem_ofFn, hx]
  rw [mem_chainLSPoints_iff, hL, ← linked_ofFn_iff_den_dvd hlam hmin hle, ← hLdef]
  constructor
  · rintro ⟨π, hπ⟩
    rw [show L = π.dirDurations by simpa using hπ]
    exact π.linked_dirDurations
  · intro h
    have hmem : ∀ p ∈ L, ∃ j, (τ j, x.weights j) = p := fun p hp ↦ List.mem_ofFn.mp hp
    refine ⟨ofLinked L (fun p hp ↦ ?_) (fun p hp ↦ ?_) ?_ h, ?_⟩
    · obtain ⟨j, rfl⟩ := hmem p hp
      exact hmin j
    · obtain ⟨j, rfl⟩ := hmem p hp
      exact x.weights_nonneg j
    · simp only [L, List.map_ofFn, Function.comp_def, List.sum_ofFn, StdSimplex.total_of_fintype]
    · rw [dirDurations_ofLinked _ _ _ _ _ ?_ ?_]
      · simp
      · intro p hp
        obtain ⟨j, rfl⟩ := hmem p hp
        exact (x.weights_nonneg j).lt_of_ne' (hx j)
      · rw [hLdef, List.isChain_ofFn]
        exact fun i hi ↦ (hne ⟨i, by omega⟩).symm

/-- **Lakshmibai–Seshadri points of an edge.** For a dominant shape and minimal coset
representatives `y < x`, a rational interior point `z` of the edge from `x` to `y` is a
Lakshmibai–Seshadri point exactly when its coordinate at `x`, the break of the path, is
`k / d_λ(x, y)` for some `0 < k < d_λ(x, y)`. -/
theorem mem_chainLSPoints_pair_iff (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) (hne : y ≠ x) {z : StdSimplex ℚ (Fin 2)}
    (hz : ∀ j, z.weights j ≠ 0) :
    z ∈ chainLSPoints b lam ![x, y] ↔ ∃ k : ℕ, 0 < k ∧ k < intervalBondGcd b lam x y ∧
      z.weights 0 = k / intervalBondGcd b lam x y := by
  have hg : intervalBondGcd b lam x y ≠ 0 :=
    (intervalBondGcd_eq_zero_iff hlam hx hy hyx).not.mpr hne.symm
  have hgpos : (0 : ℚ) < intervalBondGcd b lam x y := by exact_mod_cast Nat.pos_of_ne_zero hg
  have h0 : 0 < z.weights 0 := (z.weights_nonneg 0).lt_of_ne' (hz 0)
  have h1 : z.weights 0 < 1 := by
    linarith [z.total_fin_two, (z.weights_nonneg 1).lt_of_ne' (hz 1)]
  rw [mem_chainLSPoints_iff_den_dvd hlam (fun j ↦ by fin_cases j <;> assumption)
    (fun j ↦ by fin_cases j; exact hyx) (fun j ↦ by fin_cases j; exact hne) hz]
  have hIic : Finset.Iic (0 : Fin 2) = {0} := by decide
  simp only [Fin.forall_fin_one, Fin.castSucc_zero, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hIic, Finset.sum_singleton]
  rw [Rat.den_dvd_iff_exists_eq_intCast_div hg]
  constructor
  · rintro ⟨k, hk⟩
    rw [hk, div_pos_iff_of_pos_right hgpos] at h0
    rw [hk, div_lt_one hgpos] at h1
    have hk0 : (0 : ℤ) < k := by exact_mod_cast h0
    have hkg : k < (intervalBondGcd b lam x y : ℤ) := by exact_mod_cast h1
    have hcast : ((k.toNat : ℤ) : ℚ) = k := by rw [Int.toNat_of_nonneg hk0.le]
    exact ⟨k.toNat, by omega, by omega, by rw [hk, ← hcast, Int.cast_natCast]⟩
  · rintro ⟨k, -, -, hk⟩
    exact ⟨k, by simpa using hk⟩

/-- **The edge from `x` to `y` carries `d_λ(x, y) - 1` interior Lakshmibai–Seshadri points**, for a
dominant shape and minimal coset representatives `y < x`: one for each break `k / d_λ(x, y)`,
`0 < k < d_λ(x, y)`. -/
theorem ncard_interior_chainLSPoints_pair (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) (hne : y ≠ x) :
    {z : StdSimplex ℚ (Fin 2) | z ∈ chainLSPoints b lam ![x, y] ∧ ∀ j, z.weights j ≠ 0}.ncard =
      intervalBondGcd b lam x y - 1 := by
  set g := intervalBondGcd b lam x y
  have hg : (0 : ℚ) < g := by
    exact_mod_cast Nat.pos_of_ne_zero
      ((intervalBondGcd_eq_zero_iff hlam hx hy hyx).not.mpr hne.symm)
  -- A point of the edge is determined by its coordinate at `x`, through `StdSimplex.equivIcc`.
  have hinj : Function.Injective fun z : StdSimplex ℚ (Fin 2) ↦ z.weights 0 := by
    intro z z' (h : z.weights 0 = z'.weights 0)
    refine StdSimplex.equivIcc.injective (Subtype.ext ?_)
    simp only [StdSimplex.equivIcc_apply_coe]
    linarith [z.total_fin_two, z'.total_fin_two]
  have himage : (fun z : StdSimplex ℚ (Fin 2) ↦ z.weights 0) ''
      {z : StdSimplex ℚ (Fin 2) | z ∈ chainLSPoints b lam ![x, y] ∧ ∀ j, z.weights j ≠ 0} =
      (fun k : ℕ ↦ (k : ℚ) / g) '' Set.Ioo 0 g := by
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      obtain ⟨k, hk0, hkg, hk⟩ := (mem_chainLSPoints_pair_iff hlam hx hy hyx hne hz0).mp hz
      exact ⟨k, ⟨hk0, hkg⟩, hk.symm⟩
    · rintro ⟨k, ⟨hk0, hkg⟩, rfl⟩
      have hpos : (0 : ℚ) < k / g := div_pos (by exact_mod_cast hk0) hg
      have hlt : (k : ℚ) / g < 1 := (div_lt_one hg).mpr (by exact_mod_cast hkg)
      let z := StdSimplex.equivIcc.symm
        (⟨1 - k / g, sub_nonneg.mpr hlt.le, sub_le_self _ hpos.le⟩ : Set.Icc (0 : ℚ) 1)
      have hz1 : z.weights 1 = 1 - k / g :=
        congrArg Subtype.val (StdSimplex.equivIcc.apply_symm_apply _)
      have hz0 : z.weights 0 = k / g := by linarith [z.total_fin_two]
      have hznz : ∀ j, z.weights j ≠ 0 := fun j ↦ by
        fin_cases j
        · simpa [hz0] using hpos.ne'
        · simpa [hz1] using (sub_pos.mpr hlt).ne'
      exact ⟨z, ⟨(mem_chainLSPoints_pair_iff hlam hx hy hyx hne hznz).mpr
        ⟨k, hk0, hkg, hz0⟩, hznz⟩, hz0⟩
  rw [← Set.ncard_image_of_injective _ hinj, himage,
    Set.ncard_image_of_injective _ fun k k' h ↦ by simpa [div_left_inj₀ hg.ne'] using h,
    Set.ncard_Ioo_nat, Nat.sub_zero]

end LSPoints

end TauCeti.LSPath
