/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.ComplexProjectiveSpace.Line.Basic

/-!
# The projective line induces an isomorphism on `π₂(CPⁿ)`

An ordered orthonormal two-frame `f = (f₀, f₁)` of `ℂⁿ⁺¹` spans a complex plane, whose projective
line is the image of `ι_f : CP¹ → CPⁿ`, `[a : b] ↦ [a f₀ + b f₁]`
(`(TauCeti.ComplexProjectiveSpace.lineMap n).curry f`). The map `ι_f` is covered by the isometric
embedding `S³ → S²ⁿ⁺¹`, `(a, b) ↦ a f₀ + b f₁`, of unit spheres, which commutes with unit complex
scalars. So `ι_f` is a map of Hopf fibrations, and on the fibres over `[e₀]` and `[f₀]` it is the
identity of the circle, read through `u ↦ u • e₀` and `u ↦ u • f₀`. Naturality of the boundary map
of a Serre fibration (`TauCeti.TopCat.fibrationBoundary_map`) then shows that `ι_f` intertwines the
boundary maps `π_{k+1}(CP¹) → π_k(S¹)` and `π_{k+1}(CPⁿ) → π_k(S¹)` of the two Hopf fibrations
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_homotopyGroupMap_lineMap`).

In degree two both boundary maps are isomorphisms onto `π₁(S¹)`
(`TauCeti.ComplexProjectiveSpace.bijective_hopfBoundary`), so `ι_f` induces an isomorphism
`π₂(CP¹, [e₀]) ≅ π₂(CPⁿ, [f₀])`
(`TauCeti.ComplexProjectiveSpace.lineHomotopyGroupMulEquiv`). Composing with the homeomorphism
`CP¹ ≃ₜ S²` of the Hopf map, the projective line as a two-sphere, `σ_f : S² → CPⁿ`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamily`), induces an isomorphism
`π₂(S², north) ≅ π₂(CPⁿ, [f₀])`
(`TauCeti.ComplexProjectiveSpace.lineSphereHomotopyGroupMulEquiv`), so it sends a generator of
`π₂(S²)` to a generator of `π₂(CPⁿ)`. No sign normalization of this generator is fixed here. The
two-sphere `σ_f` is meant as input for a based loop `S¹ → ΩCPⁿ` adjoint to a projective line; that
loop is not constructed in this file.

Homotopy groups are indexed as in `TauCeti.ComplexProjectiveSpace.hopfBoundary`: `π_{k+1}` is
modelled on the cube `I^(Option N)` for a finite type `N` of cardinality `k`, so `π₂` is the case
`Nat.card N = 1`.

## Main results

* `TauCeti.ComplexProjectiveSpace.hopfBoundary_homotopyGroupMap_lineMap`: the projective line of
  `f` intertwines the boundary maps of the Hopf fibrations of `CP¹` and `CPⁿ`, in every degree.
* `TauCeti.ComplexProjectiveSpace.bijective_homotopyGroupMap_lineMap`: the projective line induces
  a bijection `π₂(CP¹, [e₀]) → π₂(CPⁿ, [f₀])`.
* `TauCeti.ComplexProjectiveSpace.bijective_homotopyGroupMap_lineSphereFamily`: the projective
  line as a two-sphere induces a bijection `π₂(S², north) → π₂(CPⁿ, [f₀])`.
* `TauCeti.ComplexProjectiveSpace.lineHomotopyGroupMulEquiv`,
  `TauCeti.ComplexProjectiveSpace.lineSphereHomotopyGroupMulEquiv`: these bijections as group
  isomorphisms.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Example 4.45.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.5 (the projective lines in the proof
  of Proposition 6.38).
-/

public section

noncomputable section

open CategoryTheory Metric

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} {N : Type*} (f : finiteOrthonormalFrame ℂ 2 (n + 1))

/-- The first standard basis vector `e₀` of `ℂ²`, a unit vector. -/
private abbrev e₀ : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The square of Hopf fibrations given by the projective line of `f`. -/
private theorem commSq_lineMap :
    CommSq (TopCat.ofHom (lineVector f)) (hopfHom 1) (hopfHom n)
      (TopCat.ofHom ((lineMap n).curry f)) :=
  ⟨by ext v; exact (lineMap_mk_lineVector f v).symm⟩

variable [Finite N]

/-- **The projective line intertwines the Hopf boundary maps.** The projective line
`ι_f : CP¹ → CPⁿ` of an orthonormal two-frame `f` carries the boundary map
`π_{k+1}(CP¹, [e₀]) → π_k(S¹, 1)` of the Hopf fibration of `CP¹` to that of `CPⁿ` at `[f₀]`:
`∂ (ι_f)_* a = ∂ a`. -/
@[simp]
theorem hopfBoundary_homotopyGroupMap_lineMap
    (a : HomotopyGroup (Option N) (ComplexProjectiveSpace 1)
      (mk 1 ⟨EuclideanSpace.single 0 1, by simp⟩)) :
    hopfBoundary (f.toSphere 0) N
        (HomotopyGroup.map ((lineMap n).curry f) (lineMap_mk_single_zero f) a) =
      hopfBoundary ⟨EuclideanSpace.single 0 1, by simp⟩ N a := by
  have hf₀ : lineVector f e₀ = f.toSphere 0 := Subtype.ext <| by simp
  -- The map of fibres over `[e₀]` and `[f₀]` given by the embedding of unit spheres.
  let φ : C((hopfHom 1).fiber (mk 1 e₀), (hopfHom n).fiber (mk n (f.toSphere 0))) :=
    ⟨fun x ↦ ⟨lineVector f x.val, by
      have hx : mk 1 x.val = mk 1 e₀ := x.property
      -- Membership in the fibre of `hopfHom n` over `[f₀]` is the equation `[x] = [f₀]` for
      -- the image `x` of the point; `change` unfolds the preimage and the morphism `hopfHom n`.
      change mk n (lineVector f x.val) = mk n (f.toSphere 0)
      rw [← lineMap_mk_lineVector, hx, lineMap_mk_lineVector, hf₀]⟩, by fun_prop⟩
  have key := TopCat.fibrationBoundary_map_of_eq (commSq_lineMap f) (mk_mem_serreFibrations 1)
    (mk_mem_serreFibrations n) (e := ⟨e₀, rfl⟩) (lineMap_mk_single_zero f)
    (e' := ⟨f.toSphere 0, rfl⟩) φ (fun _ ↦ rfl) (Subtype.ext hf₀) a
  rw [hopfBoundary_apply, hopfBoundary_apply]
  refine (congrArg _ key).trans ?_
  rw [HomotopyGroup.homeomorphEquivOfEq_apply, HomotopyGroup.homeomorphEquivOfEq_apply,
    HomotopyGroup.map_comp_apply]
  refine HomotopyGroup.map_congr (ContinuousMap.ext fun x ↦ ?_) _ _ _
  -- On the fibre over `[e₀]`, the point `u • e₀` goes to `u • f₀`, so both sides are `u`.
  obtain ⟨u, rfl⟩ := (hopfFiberHomeomorph e₀).surjective x
  refine ((hopfFiberHomeomorph (f.toSphere 0)).symm_apply_eq.2 (Subtype.ext ?_)).trans
    ((hopfFiberHomeomorph e₀).symm_apply_apply u).symm
  simp [φ, coe_hopfFiberHomeomorph_apply, lineVector_smul, hf₀]

/-- **The projective line induces an isomorphism on `π₂`.** For an orthonormal two-frame `f` of
`ℂⁿ⁺¹`, the projective line `ι_f : CP¹ → CPⁿ` induces a bijection
`π₂(CP¹, [e₀]) → π₂(CPⁿ, [f₀])`: it commutes with the boundary maps of the Hopf fibrations, which
are both bijections onto `π₁(S¹)`. -/
theorem bijective_homotopyGroupMap_lineMap [Nonempty N] (hN : Nat.card N < 2) :
    Function.Bijective
      (HomotopyGroup.map (N := Option N) ((lineMap n).curry f)
        (lineMap_mk_single_zero f)) := by
  have hn := finiteOrthonormalFrame.nonempty_iff_le.1 ⟨f⟩
  refine (Function.Bijective.of_comp_iff' (bijective_hopfBoundary (f.toSphere 0)
    (N := N) (by omega)) _).1 ?_
  rw [show hopfBoundary (f.toSphere 0) N ∘
      HomotopyGroup.map ((lineMap n).curry f) (lineMap_mk_single_zero f) =
    hopfBoundary _ N from funext (hopfBoundary_homotopyGroupMap_lineMap f)]
  exact bijective_hopfBoundary _ (by omega)

/-- **The projective line as a two-sphere induces an isomorphism on `π₂`.** For an orthonormal
two-frame `f` of `ℂⁿ⁺¹`, the two-sphere `σ_f : S² → CPⁿ`, `h (a, b) ↦ [a f₀ + b f₁]`, induces a
bijection `π₂(S², north) → π₂(CPⁿ, [f₀])`. -/
theorem bijective_homotopyGroupMap_lineSphereFamily [Nonempty N] (hN : Nat.card N < 2) :
    Function.Bijective
      (HomotopyGroup.map (N := Option N) (lineSphereFamily n f)
        (lineSphereFamily_apply_north f)) := by
  have hcomp : ((lineMap n).curry f).comp (homeomorphSphere2.symm : C(Sphere2, _)) =
      lineSphereFamily n f := ContinuousMap.ext fun x ↦ (lineSphereFamily_apply f x).symm
  rw [← HomotopyGroup.map_comp_map_of_comp_eq hcomp (lineMap_mk_single_zero f)
    homeomorphSphere2_symm_north]
  exact (bijective_homotopyGroupMap_lineMap f hN).comp
    (HomotopyGroup.homeomorphEquivOfEq homeomorphSphere2.symm
      homeomorphSphere2_symm_north).bijective

variable [DecidableEq N] [Nonempty N]

/-- The isomorphism `π₂(CP¹, [e₀]) ≃* π₂(CPⁿ, [f₀])` induced by the projective line of an
orthonormal two-frame `f`. -/
def lineHomotopyGroupMulEquiv (hN : Nat.card N < 2) :
    HomotopyGroup (Option N) (ComplexProjectiveSpace 1)
      (mk 1 ⟨EuclideanSpace.single 0 1, by simp⟩) ≃*
      HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n (f.toSphere 0)) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom ((lineMap n).curry f) (lineMap_mk_single_zero f))
    (bijective_homotopyGroupMap_lineMap f hN)

@[simp]
theorem lineHomotopyGroupMulEquiv_apply (hN : Nat.card N < 2)
    (a : HomotopyGroup (Option N) (ComplexProjectiveSpace 1)
      (mk 1 ⟨EuclideanSpace.single 0 1, by simp⟩)) :
    lineHomotopyGroupMulEquiv f hN a =
      HomotopyGroup.map ((lineMap n).curry f) (lineMap_mk_single_zero f) a :=
  (rfl)

/-- The isomorphism `π₂(S², north) ≃* π₂(CPⁿ, [f₀])` induced by the projective line of an
orthonormal two-frame `f`, parametrized by the two-sphere through the Hopf map. -/
def lineSphereHomotopyGroupMulEquiv (hN : Nat.card N < 2) :
    HomotopyGroup (Option N) Sphere2 Sphere2.north ≃*
      HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n (f.toSphere 0)) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom _ (lineSphereFamily_apply_north f))
    (bijective_homotopyGroupMap_lineSphereFamily f hN)

@[simp]
theorem lineSphereHomotopyGroupMulEquiv_apply (hN : Nat.card N < 2)
    (a : HomotopyGroup (Option N) Sphere2 Sphere2.north) :
    lineSphereHomotopyGroupMulEquiv f hN a =
      HomotopyGroup.map (lineSphereFamily n f) (lineSphereFamily_apply_north f) a :=
  (rfl)

end TauCeti.ComplexProjectiveSpace
