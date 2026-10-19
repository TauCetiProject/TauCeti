/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.Homotopy.AvoidPoint
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalVectorSpace

/-!
# Homotopy groups of spheres up to their dimension

The unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space is `(n - 1)`-connected:
`πₖ(Sⁿ, x)` is trivial for every `k < n`, in every degree including `π₀`
(`TauCeti.subsingleton_homotopyGroup_sphere_of_lt`). Consequently, by the Hurewicz theorem and
the homology of spheres, `πₙ(Sⁿ, x) ≅ ℤ` for `n ≥ 2` (`TauCeti.homotopyGroupSphereAddEquiv`),
and the double Moore loop space of `S³` has first integral homology `ℤ`
(`TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv`).

The vanishing is Hatcher's argument for Corollary 4.9. A generalized loop `Iᵏ → Sⁿ` is a map out
of the cube, a compactum of dimension `k < n`. Read through the stereographic projection from the
base point, which is a chart of `Sⁿ` onto `ℝⁿ` whose source misses the base point, it is homotopic
relative to the boundary of the cube to a generalized loop omitting a point of the sphere
(`ContinuousMap.exists_homotopyRel_notMem_range`, the smooth form of Hatcher's Lemma 4.10). The
sphere minus that point is homeomorphic to `ℝⁿ` by the stereographic projection from it, so all
its homotopy groups are trivial. Spheres of normed spaces are reduced to Euclidean ones through
`TauCeti.sphereHomeomorphOfFinrankEq`.

The isomorphism `πₙ(Sⁿ, x) ≅ ℤ` is the cubical Hurewicz isomorphism
`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv` followed by the identification
`TauCeti.reducedSingularHomologySphereIso` of `Hₙ(Sⁿ; ℤ)` with `ℤ` determined by an orthonormal
basis, so its sign depends on the orientation of that basis.

## Main declarations

* `TauCeti.subsingleton_homotopyGroup_sphere_of_lt`: `πₖ(Sⁿ, x)` is trivial for `k < n`.
* `TauCeti.homotopyGroupSphereAddEquiv`: `πₙ(Sⁿ, x) ≅ ℤ` for `n ≥ 2`, given an orthonormal basis.
* `TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv`: `H₁(ΩᴹΩᴹS³; ℤ) ≅ ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.9 and Lemma 4.10, and Section 4.2, Corollary 4.25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
-/

public section

noncomputable section

open Metric Set Module CategoryTheory
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : Type*}

/-- The unit sphere minus one point is homeomorphic to `ℝⁿ`, by stereographic projection from
that point. -/
private def sphereComplSingletonHomeomorph (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (y : sphere (0 : E) 1) :
    ({y}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source y).symm).trans <|
    (stereographic' n y).toHomeomorphSourceTarget.trans <|
      (Homeomorph.setCongr (stereographic'_target y)).trans (Homeomorph.Set.univ _)

/-- A generalized loop on the unit sphere omitting a point other than the base point is homotopic
to the constant loop: it lies in the punctured sphere, which is homeomorphic to `ℝⁿ`. -/
private theorem mk_eq_mk_const_of_notMem_range (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    {x y : sphere (0 : E) 1} (hxy : x ≠ y)
    (p : Ω^ N (sphere (0 : E) 1) x) (hp : y ∉ range p) :
    (⟦p⟧ : HomotopyGroup N (sphere (0 : E) 1) x) = ⟦GenLoop.const⟧ := by
  have hpy (t : I^N) : p t ∈ ({y}ᶜ : Set (sphere (0 : E) 1)) := fun h ↦ hp ⟨t, h⟩
  let x' : ({y}ᶜ : Set (sphere (0 : E) 1)) := ⟨x, hxy⟩
  have : Subsingleton (HomotopyGroup N ({y}ᶜ : Set (sphere (0 : E) 1)) x') :=
    (HomotopyGroup.homeomorphEquiv (N := N) (sphereComplSingletonHomeomorph n y)
      x').subsingleton_congr.mpr inferInstance
  -- The loop `p`, with values in the punctured sphere.
  let p' : Ω^ N ({y}ᶜ : Set (sphere (0 : E) 1)) x' :=
    ⟨⟨fun t ↦ ⟨p t, hpy t⟩, p.1.continuous.subtype_mk hpy⟩,
      fun t ht ↦ Subtype.ext (GenLoop.boundary p t ht)⟩
  let ι : C(({y}ᶜ : Set (sphere (0 : E) 1)), sphere (0 : E) 1) := ⟨Subtype.val, by fun_prop⟩
  have hp' : GenLoop.map ι rfl p' = p := GenLoop.ext _ _ fun t ↦ GenLoop.map_apply ι rfl p' t
  have hp'1 : (⟦p'⟧ : HomotopyGroup N ({y}ᶜ : Set (sphere (0 : E) 1)) x') = ⟦GenLoop.const⟧ :=
    this.elim _ _
  rw [← hp', ← HomotopyGroup.map_mk, hp'1, HomotopyGroup.map_mk, GenLoop.map_const]

/-- Every generalized loop of dimension `k < n` on the unit sphere of an `(n + 1)`-dimensional
real inner product space is homotopic to the constant loop. -/
private theorem mk_eq_mk_const_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] [Finite N]
    (hN : Nat.card N < n) (x : sphere (0 : E) 1)
    (p : Ω^ N (sphere (0 : E) 1) x) :
    (⟦p⟧ : HomotopyGroup N (sphere (0 : E) 1) x) = ⟦GenLoop.const⟧ := by
  have := Fintype.ofFinite N
  -- Read the loop on the closed unit ball of `N → ℝ`, and push it off a point of the
  -- stereographic chart at the base point, relative to the points that are not sent into the
  -- chart. These include the boundary of the cube, which is sent to the base point.
  let e := cubeHomeomorphClosedBall N
  let φ := stereographic' n x
  let f : C(closedBall (0 : N → ℝ) 1, sphere (0 : E) 1) :=
    (p : C(I^N, sphere (0 : E) 1)).comp (e.symm : C(closedBall (0 : N → ℝ) 1, I^N))
  have hdim : finrank ℝ (N → ℝ) < finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rwa [finrank_fintype_fun_eq_card, finrank_euclideanSpace_fin, ← Nat.card_eq_fintype_card]
  have hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ φ.target := by
    simp [φ, stereographic'_target]
  obtain ⟨g, ⟨H⟩, -, q, hq, hgq⟩ :=
    ContinuousMap.exists_homotopyRel_notMem_range f isClosed_closedBall hdim φ one_pos hball
  -- The chart source omits the base point, so the missed point is not the base point, and the
  -- homotopy fixes every point sent to the base point.
  have hsource {z : sphere (0 : E) 1} (hz : z ∈ φ.symm '' ball 0 1) : z ≠ x := by
    obtain ⟨w, hw, rfl⟩ := hz
    simpa [φ, stereographic'_source] using φ.map_target (hball hw)
  have hfe (t : I^N) : f (e t) = p t := congrArg p (e.symm_apply_apply t)
  have hfix {t : I^N} (ht : t ∈ Cube.boundary N) :
      e t ∈ (f ⁻¹' (φ.symm '' ball 0 1))ᶜ := fun h ↦
    hsource h ((hfe t).trans (GenLoop.boundary p t ht))
  let p' : Ω^ N (sphere (0 : E) 1) x :=
    ⟨g.comp (e : C(I^N, closedBall (0 : N → ℝ) 1)), fun t ht ↦
      ((H.fst_eq_snd (hfix ht)).symm.trans (hfe t)).trans (GenLoop.boundary p t ht)⟩
  have hpp' : (⟦p⟧ : HomotopyGroup N (sphere (0 : E) 1) x) = ⟦p'⟧ := by
    refine Quotient.sound ⟨{ toHomotopy := (H.toHomotopy.compContinuousMap
        (e : C(I^N, closedBall (0 : N → ℝ) 1))).cast (ContinuousMap.ext hfe) rfl, prop' := ?_ }⟩
    exact fun s t ht ↦ (H.eq_fst s (hfix ht)).trans (hfe t)
  rw [hpp']
  exact mk_eq_mk_const_of_notMem_range n (hsource ⟨q, hq, rfl⟩).symm p'
    fun ⟨t, ht⟩ ↦ hgq ⟨e t, ht⟩

end InnerProduct

/-- **Spheres are `(n - 1)`-connected** (Hatcher, Corollary 4.9). For the unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real normed space, the homotopy set `πₖ(Sⁿ, x)` is trivial for every
`k = Nat.card N < n`. In degree zero this says that `Sⁿ` is path connected for `n ≥ 1`. -/
theorem subsingleton_homotopyGroup_sphere_of_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hE : finrank ℝ E = n + 1)
    {N : Type*} [Finite N] (hN : Nat.card N < n) (x : sphere (0 : E) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) := by
  let F := EuclideanSpace ℝ (Fin (n + 1))
  have : Fact (finrank ℝ F = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let h := sphereHomeomorphOfFinrankEq (hE.trans finrank_euclideanSpace_fin.symm :
    finrank ℝ E = finrank ℝ F)
  refine (HomotopyGroup.homeomorphEquiv (N := N) h x).subsingleton_congr.mpr ⟨fun a b ↦ ?_⟩
  induction a using Quotient.inductionOn with | h p => ?_
  induction b using Quotient.inductionOn with | h q => ?_
  exact (mk_eq_mk_const_sphere hN _ p).trans (mk_eq_mk_const_sphere hN _ q).symm

section Hurewicz

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- `TauCeti.subsingleton_homotopyGroup_sphere_of_lt`, with the dimension read off an orthonormal
basis. -/
private theorem subsingleton_homotopyGroup_sphere_of_basis {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) {N : Type} [Finite N] (hN : Nat.card N < m)
    (x : sphere (0 : E) 1) : Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) :=
  have := Module.Finite.of_basis b.toBasis
  subsingleton_homotopyGroup_sphere_of_lt (by simp [finrank_eq_card_basis b.toBasis]) hN x

/-- **The `n`-th homotopy group of `Sⁿ` is `ℤ`** for `n ≥ 2` (Hatcher, Corollary 4.25). For the
unit sphere of a real inner product space with an orthonormal basis `b` indexed by `Fin (n + 3)`,
this is the cubical Hurewicz isomorphism `π_{n+2}(S^{n+2}, x) ≅ H_{n+2}(S^{n+2}; ℤ)` followed by
the identification of `H_{n+2}(S^{n+2}; ℤ)` with `ℤ` determined by `b`. -/
def homotopyGroupSphereAddEquiv (b : OrthonormalBasis (Fin (n + 3)) ℝ E)
    (x : sphere (0 : E) 1) :
    Additive (π_ (n + 2) (sphere (0 : E) 1) x) ≃+ ℤ :=
  (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv fun _ hk ↦
      subsingleton_homotopyGroup_sphere_of_basis b (by simpa using hk) x).trans
    (((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (n + 1)).app _).symm ≪≫
      reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ) b).toLinearEquiv.toAddEquiv

/-- `TauCeti.homotopyGroupSphereAddEquiv` is the cubical Hurewicz isomorphism followed by the
identification of the top homology of the sphere with `ℤ`. -/
theorem homotopyGroupSphereAddEquiv_apply (b : OrthonormalBasis (Fin (n + 3)) ℝ E)
    (x : sphere (0 : E) 1)
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) x))
    (a : Additive (π_ (n + 2) (sphere (0 : E) 1) x)) :
    homotopyGroupSphereAddEquiv b x a =
      (reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ) b).hom.hom
        (((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (n + 1)).inv.app _).hom
          (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hX a)) :=
  (rfl)

/-- **The first homology of the double loop space of `S³` is `ℤ`.** For the unit sphere `S³` of
a real inner product space with an orthonormal basis `b` indexed by `Fin 4`, the first integral
homology of the double Moore loop space `ΩᴹΩᴹS³` is `π₃(S³) ≅ ℤ`, through degree-one Hurewicz
(`TauCeti.MooreLoopSpace.doubleFirstHomologyAddEquiv`) and
`TauCeti.homotopyGroupSphereAddEquiv`. -/
def MooreLoopSpace.doubleFirstHomologySphereAddEquiv (b : OrthonormalBasis (Fin 4) ℝ E)
    (x : sphere (0 : E) 1) :
    ((singularChains ℤ).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1))).homology 1 ≃+ ℤ :=
  have : Subsingleton (π_ 2 (sphere (0 : E) 1) x) :=
    subsingleton_homotopyGroup_sphere_of_basis b (by simp) x
  (doubleFirstHomologyAddEquiv x).symm.trans (homotopyGroupSphereAddEquiv (n := 1) b x)

end Hurewicz

end TauCeti
