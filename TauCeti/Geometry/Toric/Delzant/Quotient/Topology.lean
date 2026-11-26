/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Toric.Delzant.Hirzebruch
public import TauCeti.Geometry.Toric.Delzant.Quotient.Hamiltonian
public import TauCeti.Geometry.Toric.Delzant.Quotient.Vertex
public import TauCeti.Geometry.Toric.Delzant.Simplex
import TauCeti.Algebra.AddCircle
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect
import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Topology.Connected.TypeTags

/-!
# The topology of Delzant toric manifolds

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ`, with Delzant quotient `M_Δ` (`TauCeti.Toric.DelzantQuotient i u c`), its symplectic form
`ω_Δ` and the Hamiltonian action of the torus `T = (ℝ / 2πℤ)^ι`
(`TauCeti.Toric.IsDelzant.hamiltonianTorusData_delzantQuotientSymplecticForm`). This file
computes the basic topology of `M_Δ` from the polytope:

* `M_Δ` is connected (`TauCeti.Toric.IsDelzant.connectedSpace_delzantQuotient`);
* `M_Δ` is simply connected (`TauCeti.Toric.IsDelzant.simplyConnectedSpace_delzantQuotient`);
* its odd Betti numbers vanish, for every division ring of coefficients
  (`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_zero_of_odd`);
* the sum of its Betti numbers is the number of vertices of `Δ`
  (`TauCeti.Toric.IsDelzant.sum_bettiNumber_delzantQuotient`).

**Connectedness.** The reduced moment map `μ_Δ : M_Δ → Δ` is a continuous surjection from a
compact space onto a Hausdorff space, hence a quotient map. Its fibres are the orbits of the torus
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_eq_reducedMomentMap_iff`), which are connected as
continuous images of `ℝ^ι`, and its target `Δ` is convex and nonempty. A quotient map with
connected fibres onto a connected space has connected source
(`TauCeti.Toric.DelzantQuotient.connectedSpace`). Only the boundedness and nonemptiness of `Δ`
are used here, not the Delzant conditions.

**Perfect moment components.** The fixed points of the torus on `M_Δ` lie exactly over the
vertices of `Δ`, one over each vertex
(`TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`). So there are as many fixed
points as vertices (`TauCeti.Toric.DelzantQuotient.ncard_fixedPoints_multiplicative`), finitely
many, and each of them is isolated
(`TauCeti.Toric.DelzantQuotient.eventually_eq_of_mem_fixedPoints_multiplicative`). For a torus
acting by symplectomorphisms of a compact manifold with a moment map and isolated fixed points, a
generic component of the moment map is a perfect Morse function whose critical points are the
fixed points, all of even index
(`TauCeti.SmoothTwoForm.IsMomentMap.bettiNumber_eq_zero_of_odd`,
`TauCeti.SmoothTwoForm.IsMomentMap.sum_bettiNumber_eq_ncard_fixedPoints`), and since it has no
critical point of index one, a connected such manifold is simply connected
(`TauCeti.SmoothTwoForm.IsMomentMap.simplyConnectedSpace`). The model space of `M_Δ` has dimension
`2 n` with `n = dim V` (`TauCeti.Toric.IsDelzant.finrank_delzantQuotientModelSpace`), which bounds
the range of the Betti numbers.

For instance, the Delzant quotient of the standard `n`-simplex, which is `ℂPⁿ`
(`TauCeti.Toric.DelzantQuotient.simplexHomeomorph`), has total Betti number `n + 1`
(`TauCeti.Toric.sum_bettiNumber_delzantQuotient_simplex`), and that of a Hirzebruch trapezoid,
four (`TauCeti.Toric.sum_bettiNumber_delzantQuotient_hirzebruch`).

The homology here is singular homology with coefficients in a division ring. The individual even
Betti numbers, counted at each vertex by the edges along which a generic linear function
decreases, are computed in `TauCeti.Geometry.Toric.Delzant.Quotient.Betti`; the freeness and ring
structure of the integral cohomology are not proved here.

## Main results

* `TauCeti.Toric.DelzantQuotient.connectedSpace`: the Delzant quotient of a nonempty bounded
  polyhedron is connected.
* `TauCeti.Toric.DelzantQuotient.ncard_fixedPoints_multiplicative`: the torus has as many fixed
  points on the Delzant quotient as `Δ` has vertices.
* `TauCeti.Toric.IsDelzant.connectedSpace_delzantQuotient`,
  `TauCeti.Toric.IsDelzant.simplyConnectedSpace_delzantQuotient`: a Delzant toric manifold is
  connected and simply connected.
* `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_zero_of_odd`,
  `TauCeti.Toric.IsDelzant.sum_bettiNumber_delzantQuotient`: its odd Betti numbers vanish, and
  its Betti numbers add up to the number of vertices of `Δ`.
* `TauCeti.Toric.sum_bettiNumber_delzantQuotient_simplex`,
  `TauCeti.Toric.sum_bettiNumber_delzantQuotient_hirzebruch`: the total Betti numbers of `ℂPⁿ`
  and of the Hirzebruch surfaces.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1, Homework 21 and Section 29.
-/

public section

noncomputable section

open Module Set Real Topology
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

universe w

variable {ι : Type w} {N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace DelzantQuotient

/-! ### Connectedness -/

section Connected

variable [FiniteDimensional ℝ V]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

/-- The fibre of the reduced moment map through `q` is the orbit of `q` under the torus, the image
of `ℝ^ι` under `t ↦ [t] +ᵥ q`. -/
private theorem reducedMomentMap_preimage_singleton (q : DelzantQuotient i u c) :
    reducedMomentMap hβ ⁻¹' {reducedMomentMap hβ q} =
      range fun t : ι → ℝ ↦ (fun j ↦ (t j : AddCircle (2 * π))) +ᵥ q := by
  ext q'
  rw [mem_preimage, mem_singleton_iff, reducedMomentMap_eq_reducedMomentMap_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with | H θ =>
    obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
    exact ⟨t, (coe_vadd _ q).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, coe_vadd _ q⟩

/-- **The Delzant quotient of a nonempty bounded polyhedron is connected.** The reduced moment map
is a quotient map onto the convex set `Δ`, with connected fibres, the orbits of the torus. -/
theorem connectedSpace (hb : Bornology.IsBounded (facetPolyhedron i u c))
    (hne : (facetPolyhedron i u c).Nonempty) : ConnectedSpace (DelzantQuotient i u c) := by
  have := compactSpace_delzantQuotient (c := c) hb
  have : ConnectedSpace (facetPolyhedron i u c) :=
    isConnected_iff_connectedSpace.1 (convex_facetPolyhedron.isConnected hne)
  let f : DelzantQuotient i u c → facetPolyhedron i u c :=
    fun q ↦ ⟨reducedMomentMap hβ q, reducedMomentMap_mem_facetPolyhedron hβ q⟩
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← range_reducedMomentMap hβ] at hy
    obtain ⟨q, rfl⟩ := hy
    exact ⟨q, rfl⟩
  have hf : IsQuotientMap f :=
    .of_surjective_continuous hfs ((continuous_reducedMomentMap hβ).subtype_mk _)
  -- The fibres of `f` are the fibres of `μ_Δ`, the orbits of the torus.
  have hfib (y : facetPolyhedron i u c) : IsConnected (f ⁻¹' {y}) := by
    obtain ⟨q, rfl⟩ := hfs y
    have hfq : f ⁻¹' {f q} = reducedMomentMap hβ ⁻¹' {reducedMomentMap hβ q} := by
      ext q'
      simp only [mem_preimage, mem_singleton_iff, f, Subtype.mk.injEq]
    rw [hfq, reducedMomentMap_preimage_singleton hβ]
    exact isConnected_range ((continuous_pi fun j ↦
      (AddCircle.continuous_mk' (2 * π)).comp (continuous_apply j)).vadd continuous_const)
  rw [connectedSpace_iff_univ, ← preimage_univ (f := f)]
  exact hf.isCoinducing.isConnected_preimage_of_isClosed hfib isClosed_univ isConnected_univ

end Connected

/-! ### Fixed points -/

section FixedPoints

/-- A point of the Delzant quotient is fixed by the multiplicative copy of the torus
`(ℝ / 2πℤ)^ι`, the group acting in the Lie group statements, exactly when it is fixed by the
residual torus. -/
theorem mem_fixedPoints_multiplicative_iff {q : DelzantQuotient i u c} :
    q ∈ MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π))) (DelzantQuotient i u c) ↔
      q ∈ AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c) := by
  rw [MulAction.mem_fixedPoints, AddAction.mem_fixedPoints]
  constructor
  · intro h θ
    induction θ using QuotientAddGroup.induction_on with | H θ =>
    exact (coe_vadd θ q).trans ((toAdd_vadd (Multiplicative.ofAdd θ) q).trans (h _))
  · intro h g
    rw [← toAdd_vadd, ← coe_vadd]
    exact h _

/-- The fixed points of the multiplicative copy of the torus `(ℝ / 2πℤ)^ι` on the Delzant quotient
are those of the residual torus. -/
theorem fixedPoints_multiplicative_eq :
    MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π))) (DelzantQuotient i u c) =
      AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c) :=
  Set.ext fun _ ↦ mem_fixedPoints_multiplicative_iff

variable (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

/-- **There are as many fixed points as vertices.** The torus `(ℝ / 2πℤ)^ι` has exactly as many
fixed points on the Delzant quotient as the polyhedron `Δ` has vertices, one over each vertex. -/
theorem ncard_fixedPoints_multiplicative (hi : IsIntegralLattice i) :
    (MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c)).ncard = ((facetPolyhedron i u c).extremePoints ℝ).ncard := by
  rw [fixedPoints_multiplicative_eq, (bijOn_reducedMomentMap_fixedPoints hβ hi).ncard_eq]

/-- The torus has finitely many fixed points on the Delzant quotient. -/
theorem finite_fixedPoints_multiplicative (hi : IsIntegralLattice i) :
    (MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c)).Finite := by
  rw [fixedPoints_multiplicative_eq]
  exact (bijOn_reducedMomentMap_fixedPoints hβ hi).finite_iff_finite.2
    finite_extremePoints_facetPolyhedron

/-- **Fixed points are isolated.** Near a fixed point `p` of the torus on the Delzant quotient, the
only fixed point is `p` itself, as there are finitely many fixed points. -/
theorem eventually_eq_of_mem_fixedPoints_multiplicative (hi : IsIntegralLattice i)
    {p : DelzantQuotient i u c}
    (hp : p ∈ MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c)) :
    ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c) → q = p := by
  have := hi.t2Space_delzantQuotient (u := u) (c := c)
  rw [← eventually_nhdsWithin_iff,
    (finite_fixedPoints_multiplicative hβ hi).isDiscrete.nhdsWithin p hp]
  exact Filter.eventually_pure.2 rfl

end FixedPoints

end DelzantQuotient

/-! ### Delzant toric manifolds -/

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **A Delzant toric manifold is connected.** -/
theorem connectedSpace_delzantQuotient : ConnectedSpace (DelzantQuotient i u c) :=
  have := hi.finiteDimensional
  DelzantQuotient.connectedSpace
    (surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination)
    hΔ.isBounded hΔ.nonempty

/-- The Morse theory of a generic component of the moment map of a Delzant toric manifold, done
once: the manifold is simply connected and, for every division ring of coefficients, its odd Betti
numbers vanish and its Betti numbers add up to the number of vertices of `Δ`. -/
private theorem simplyConnectedSpace_and_bettiNumber_delzantQuotient :
    SimplyConnectedSpace (DelzantQuotient i u c) ∧
      ∀ (k : Type w) [DivisionRing k],
        (∀ j, Odd j → bettiNumber k (DelzantQuotient i u c) j = 0) ∧
        ∑ j ∈ Finset.range (2 * finrank ℝ V + 1), bettiNumber k (DelzantQuotient i u c) j =
          ((facetPolyhedron i u c).extremePoints ℝ).ncard := by
  have := hi.finiteDimensional
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  have := hi.t2Space_delzantQuotient (u := u) (c := c)
  have := compactSpace_delzantQuotient (c := c) hΔ.isBounded
  have := hΔ.connectedSpace_delzantQuotient hi
  have h := hΔ.hamiltonianTorusData_delzantQuotientSymplecticForm hi hβ
  have hσ := (hΔ.isSymplectic_delzantQuotientSymplecticForm hi).isNondegenerate
  have hσG := fun g ↦
    ((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq _).2 (h.mpullback_smul g)).apply
  have hiso (p) (hp : p ∈ MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c)) :=
    DelzantQuotient.eventually_eq_of_mem_fixedPoints_multiplicative hβ hi hp
  refine ⟨h.toIsMomentMap.simplyConnectedSpace hσ hσG hiso, fun k _ ↦
    ⟨fun _ ↦ h.toIsMomentMap.bettiNumber_eq_zero_of_odd hσ hσG k hiso, ?_⟩⟩
  rw [← hΔ.finrank_delzantQuotientModelSpace hi,
    ← DelzantQuotient.ncard_fixedPoints_multiplicative hβ hi]
  exact h.toIsMomentMap.sum_bettiNumber_eq_ncard_fixedPoints hσ hσG k hiso

/-- **A Delzant toric manifold is simply connected.** A generic component of the moment map is a
Morse function whose critical points are the fixed points of the torus, all of even index, so it
attaches no one-cell. -/
theorem simplyConnectedSpace_delzantQuotient : SimplyConnectedSpace (DelzantQuotient i u c) :=
  (simplyConnectedSpace_and_bettiNumber_delzantQuotient hΔ hi).1

variable (k : Type w) [DivisionRing k]

/-- **The odd Betti numbers of a Delzant toric manifold vanish**, for every division ring of
coefficients: a generic component of the moment map is a perfect Morse function all of whose
indices are even. -/
theorem bettiNumber_delzantQuotient_eq_zero_of_odd {j : ℕ} (hj : Odd j) :
    bettiNumber k (DelzantQuotient i u c) j = 0 :=
  ((simplyConnectedSpace_and_bettiNumber_delzantQuotient hΔ hi).2 k).1 j hj

/-- **The total Betti number of a Delzant toric manifold is the number of vertices** of its
polytope `Δ`, for every division ring of coefficients. The manifold has dimension `2 n`, with
`n = dim V`; the Betti numbers add up to the number of fixed points of the torus, and there is
exactly one fixed point over each vertex. -/
theorem sum_bettiNumber_delzantQuotient :
    ∑ j ∈ Finset.range (2 * finrank ℝ V + 1), bettiNumber k (DelzantQuotient i u c) j =
      ((facetPolyhedron i u c).extremePoints ℝ).ncard :=
  ((simplyConnectedSpace_and_bettiNumber_delzantQuotient hΔ hi).2 k).2

end IsDelzant

/-! ### Examples -/

/-- **The total Betti number of `ℂPⁿ` is `n + 1`.** The Delzant quotient of the standard
`n`-simplex of size `a > 0`, which is `ℂPⁿ`
(`TauCeti.Toric.DelzantQuotient.simplexHomeomorph`), has total Betti number `n + 1`, the number
of vertices of the simplex. -/
theorem sum_bettiNumber_delzantQuotient_simplex {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a)
    (k : Type) [DivisionRing k] :
    ∑ j ∈ Finset.range (2 * n + 1), bettiNumber k (DelzantQuotient
      ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n)) (simplexSupport a)) j =
      n + 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa [ncard_extremePoints_facetPolyhedron_simplex ha] using
    (isDelzant_simplex ha).sum_bettiNumber_delzantQuotient (isIntegralLattice_intCast n) k

/-- **The total Betti number of a Hirzebruch surface is `4`.** The Delzant quotient of a
Hirzebruch trapezoid, the toric Hirzebruch surface (`S² × S²` when `m = 0`), has total Betti
number `4`, the number of vertices of the trapezoid. -/
theorem sum_bettiNumber_delzantQuotient_hirzebruch {m : ℤ} {a b : ℝ} (hb : 0 < b) (ha : 0 < a)
    (hab : m * b < a) (k : Type) [DivisionRing k] :
    ∑ j ∈ Finset.range 5, bettiNumber k (DelzantQuotient
      ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal m) (hirzebruchSupport a b)) j =
      4 := by
  simpa [ncard_extremePoints_facetPolyhedron_hirzebruch hb ha hab] using
    (isDelzant_hirzebruch hb ha hab).sum_bettiNumber_delzantQuotient (isIntegralLattice_intCast 2) k

end TauCeti.Toric
