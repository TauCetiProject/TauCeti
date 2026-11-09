/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.NumberTheory.Zsqrtd.GaussianInt
public import TauCeti.Topology.Algebra.Group.Heisenberg

/-!
# The Iwasawa manifold

The **Iwasawa manifold** is the compact complex threefold `H(ℤ[i]) \ H(ℂ)`, the quotient of the
complex Heisenberg group `H(ℂ)` by its lattice of Gaussian-integer points, acting by left
multiplication. Here `H(R)` is `TauCeti.HeisenbergGroup R`, with product
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`. It is the standard example of a compact
complex manifold that is complex parallelizable but not Kähler, and of a compact complex manifold
whose Frölicher spectral sequence does not degenerate at the first page.

This file constructs it as a quotient of `ℂ³`. The cover `TauCeti.IwasawaManifold.Cover`, with
coordinates `(x, y, z)`, is identified with `H(ℂ)` by `TauCeti.IwasawaManifold.Cover.toHeisenberg`,
and `H(ℂ)` acts on it by left multiplication,

`(a, b, c) • (x, y, z) = (a + x, b + y, c + z + a y)`.

Each element acts by an affine map whose linear part is the complex-linear shear
`(x, y, z) ↦ (x, y, z + a y)` (`TauCeti.IwasawaManifold.Cover.shear`), so `H(ℂ)` acts by
holomorphic maps. The deck group `Γ = H(ℤ[i])` (`TauCeti.IwasawaManifold.DeckGroup`) acts through
the inclusion `H(ℤ[i]) → H(ℂ)`, freely and properly discontinuously, so
`TauCeti.instIsManifoldQuotient` makes the orbit space `TauCeti.IwasawaManifold` a complex
manifold modelled on `ℂ³`, and the projection `TauCeti.IwasawaManifold.mk` is a holomorphic local
diffeomorphism. The orbit space is Hausdorff, second countable, connected and compact: every orbit
meets the product of three half-open unit squares
(`TauCeti.IwasawaManifold.Cover.exists_smul_mem_reProdIm_Ico`).

## Main definitions

* `TauCeti.IwasawaManifold.Cover`: the cover `ℂ³`, with coordinates `x`, `y`, `z`.
* `TauCeti.IwasawaManifold.Cover.toHeisenberg`: the identification of the cover with the complex
  Heisenberg group.
* `TauCeti.IwasawaManifold.DeckGroup`: the deck group `H(ℤ[i])`, acting on the cover.
* `TauCeti.IwasawaManifold`: the Iwasawa manifold, the orbit space of the deck group.
* `TauCeti.IwasawaManifold.mk`: the projection from the cover.

## Main results

* `TauCeti.IwasawaManifold.Cover.toHeisenberg_smul`,
  `TauCeti.IwasawaManifold.Cover.toHeisenberg_deck_smul`: the complex Heisenberg group, and the
  deck group through its inclusion, act on the cover by left multiplication.
* `TauCeti.IwasawaManifold.Cover.smul_eq_shear_add`, `TauCeti.IwasawaManifold.Cover.mfderiv_smul`:
  each element of `H(ℂ)` acts by an affine map with linear part a shear, which is therefore its
  differential at every point.
* `TauCeti.IwasawaManifold.Cover.instContMDiffConstSMul`,
  `TauCeti.IwasawaManifold.Cover.instContMDiffConstSMulDeckGroup`: `H(ℂ)` and the deck group act
  by holomorphic maps.
* `TauCeti.IwasawaManifold.Cover.instProperlyDiscontinuousSMul`,
  `TauCeti.IwasawaManifold.Cover.instIsCancelSMul`: the deck group acts properly discontinuously
  and freely.
* `TauCeti.IwasawaManifold.isLocalDiffeomorph_mk`, `TauCeti.IwasawaManifold.mdifferentiable_mk`:
  the projection is a local biholomorphism, and in particular holomorphic.
* `TauCeti.IwasawaManifold.mk_eq_mk_iff`: its fibres are the orbits of the deck group.
* `TauCeti.IwasawaManifold.instCompactSpace`: the Iwasawa manifold is compact.

## Implementation notes

The construction adapts the Kodaira–Thurston manifold
(`TauCeti.Geometry.Manifold.Instances.KodairaThurston`), with `ℂ` in place of `ℝ`, the
Gaussian-integer lattice in place of `ℤ`, and no circle factor: the type synonym cover with its
coordinate API, the shear-based affine description of the action and its smoothness and
differential, and the freeness, proper discontinuity and compactness proofs follow that file.

## References

* I. Nakamura, *Complex parallelisable manifolds and their small deformations*, Journal of
  Differential Geometry 10 (1975), 85–112.
* D. Angella, *The cohomologies of the Iwasawa manifold and of its small deformations*, Journal of
  Geometric Analysis 23 (2013), 1355–1378.
-/

public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace IwasawaManifold

/-- The covering space `ℂ³` of the Iwasawa manifold, with coordinates `(x, y, z)`: a type synonym
of `ℂ × ℂ × ℂ` carrying the left multiplication action of the complex Heisenberg group. -/
def Cover : Type := ℂ × ℂ × ℂ

namespace Cover

instance : NormedAddCommGroup Cover := inferInstanceAs (NormedAddCommGroup (ℂ × ℂ × ℂ))

instance : NormedSpace ℂ Cover := inferInstanceAs (NormedSpace ℂ (ℂ × ℂ × ℂ))

instance : FiniteDimensional ℂ Cover := inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ × ℂ))

instance : ProperSpace Cover := inferInstanceAs (ProperSpace (ℂ × ℂ × ℂ))

instance : SecondCountableTopology Cover := inferInstanceAs (SecondCountableTopology (ℂ × ℂ × ℂ))

/-- The coordinates `(x, y, z)` of a point of the cover, as a complex-linear equivalence with
`ℂ × ℂ × ℂ`. -/
def toProd : Cover ≃L[ℂ] ℂ × ℂ × ℂ := ContinuousLinearEquiv.refl ℂ _

/-- The cover has complex dimension three. -/
@[simp]
theorem finrank_eq : Module.finrank ℂ Cover = 3 := by
  rw [toProd.toLinearEquiv.finrank_eq]
  simp

/-- The point of the cover with coordinates `(x, y, z)`. -/
def mk (x y z : ℂ) : Cover := toProd.symm (x, y, z)

/-- The `x`-coordinate of a point of the cover. -/
def x (p : Cover) : ℂ := (toProd p).1

/-- The `y`-coordinate of a point of the cover. -/
def y (p : Cover) : ℂ := (toProd p).2.1

/-- The `z`-coordinate of a point of the cover. -/
def z (p : Cover) : ℂ := (toProd p).2.2

/-- The product representation of a point consists of its three coordinates. -/
@[simp]
theorem toProd_apply (p : Cover) : toProd p = (p.x, p.y, p.z) := (rfl)

/-- The inverse product representation constructs a point from its coordinates. -/
@[simp]
theorem toProd_symm_apply (a b c : ℂ) : toProd.symm (a, b, c) = mk a b c := (rfl)

@[simp] theorem x_mk (a b c : ℂ) : (mk a b c).x = a := (rfl)

@[simp] theorem y_mk (a b c : ℂ) : (mk a b c).y = b := (rfl)

@[simp] theorem z_mk (a b c : ℂ) : (mk a b c).z = c := (rfl)

/-- A point of the cover is determined by its coordinates. -/
@[ext]
theorem ext {p q : Cover} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q :=
  toProd.injective (Prod.ext hx (Prod.ext hy hz))

@[simp] theorem mk_x_y_z (p : Cover) : mk p.x p.y p.z = p := (rfl)

@[simp] theorem x_add (p q : Cover) : (p + q).x = p.x + q.x := (rfl)

@[simp] theorem y_add (p q : Cover) : (p + q).y = p.y + q.y := (rfl)

@[simp] theorem z_add (p q : Cover) : (p + q).z = p.z + q.z := (rfl)

@[simp] theorem x_neg (p : Cover) : (-p).x = -p.x := (rfl)

@[simp] theorem y_neg (p : Cover) : (-p).y = -p.y := (rfl)

@[simp] theorem z_neg (p : Cover) : (-p).z = -p.z := (rfl)

@[simp] theorem x_sub (p q : Cover) : (p - q).x = p.x - q.x := (rfl)

@[simp] theorem y_sub (p q : Cover) : (p - q).y = p.y - q.y := (rfl)

@[simp] theorem z_sub (p q : Cover) : (p - q).z = p.z - q.z := (rfl)

@[simp] theorem x_zero : (0 : Cover).x = 0 := (rfl)

@[simp] theorem y_zero : (0 : Cover).y = 0 := (rfl)

@[simp] theorem z_zero : (0 : Cover).z = 0 := (rfl)

@[simp] theorem x_smul (c : ℂ) (p : Cover) : (c • p).x = c * p.x := (rfl)

@[simp] theorem y_smul (c : ℂ) (p : Cover) : (c • p).y = c * p.y := (rfl)

@[simp] theorem z_smul (c : ℂ) (p : Cover) : (c • p).z = c * p.z := (rfl)

/-- The `x`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_x : Continuous x := continuous_fst.comp toProd.continuous

/-- The `y`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_y : Continuous y := continuous_snd.fst.comp toProd.continuous

/-- The `z`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_z : Continuous z := continuous_snd.snd.comp toProd.continuous

/-- The identification of the cover with the complex Heisenberg group, sending the point with
coordinates `(x, y, z)` to the group element `(x, y, z)`. -/
def toHeisenberg : Cover ≃ₜ HeisenbergGroup ℂ :=
  toProd.toHomeomorph.trans HeisenbergGroup.homeomorphProd.symm

/-- The group element corresponding to the point with coordinates `(x, y, z)` is `(x, y, z)`. -/
theorem toHeisenberg_apply (p : Cover) : toHeisenberg p = ⟨p.x, p.y, p.z⟩ := by
  simp [toHeisenberg]

@[simp] theorem x_toHeisenberg (p : Cover) : (toHeisenberg p).x = p.x := by
  simp [toHeisenberg_apply]

@[simp] theorem y_toHeisenberg (p : Cover) : (toHeisenberg p).y = p.y := by
  simp [toHeisenberg_apply]

@[simp] theorem z_toHeisenberg (p : Cover) : (toHeisenberg p).z = p.z := by
  simp [toHeisenberg_apply]

/-- The point of the cover corresponding to a group element `(a, b, c)` has coordinates
`(a, b, c)`. -/
@[simp]
theorem toHeisenberg_symm_apply (g : HeisenbergGroup ℂ) : toHeisenberg.symm g = mk g.x g.y g.z :=
  toHeisenberg.symm_apply_eq.2 (by simp [toHeisenberg_apply])

/-- The shear `(x, y, z) ↦ (x, y, z + a y)`, the linear part of left multiplication by an element
of the complex Heisenberg group whose `x`-coordinate is `a`. -/
def shear (a : ℂ) : Cover →L[ℂ] Cover :=
  LinearMap.toContinuousLinearMap
    { toFun p := mk p.x p.y (p.z + a * p.y)
      map_add' p q := by
        ext <;> simp only [x_mk, y_mk, z_mk, x_add, y_add, z_add]; ring
      map_smul' c p := by
        ext <;> simp only [x_mk, y_mk, z_mk, x_smul, y_smul, z_smul, RingHom.id_apply]; ring }

/-- The shear in coordinates. -/
@[simp]
theorem shear_apply (a : ℂ) (p : Cover) : shear a p = mk p.x p.y (p.z + a * p.y) := (rfl)

/-- The complex Heisenberg group acts on the cover by left multiplication. -/
instance : SMul (HeisenbergGroup ℂ) Cover where
  smul g p := mk (g.x + p.x) (g.y + p.y) (g.z + p.z + g.x * p.y)

/-- An element `(a, b, c)` of the complex Heisenberg group acts by
`(x, y, z) ↦ (a + x, b + y, c + z + a y)`. -/
theorem smul_def (g : HeisenbergGroup ℂ) (p : Cover) :
    g • p = mk (g.x + p.x) (g.y + p.y) (g.z + p.z + g.x * p.y) :=
  (rfl)

/-- An element `(a, b, c)` of the complex Heisenberg group sends the point with coordinates
`(x, y, z)` to the point with coordinates `(a + x, b + y, c + z + a y)`. -/
@[simp]
theorem smul_mk (g : HeisenbergGroup ℂ) (a b c : ℂ) :
    g • mk a b c = mk (g.x + a) (g.y + b) (g.z + c + g.x * b) :=
  (rfl)

/-- Left multiplication translates the `x`-coordinate. -/
@[simp]
theorem x_smul_heisenberg (g : HeisenbergGroup ℂ) (p : Cover) : (g • p).x = g.x + p.x := (rfl)

/-- Left multiplication translates the `y`-coordinate. -/
@[simp]
theorem y_smul_heisenberg (g : HeisenbergGroup ℂ) (p : Cover) : (g • p).y = g.y + p.y := (rfl)

/-- Left multiplication shears and translates the `z`-coordinate. -/
@[simp]
theorem z_smul_heisenberg (g : HeisenbergGroup ℂ) (p : Cover) :
    (g • p).z = g.z + p.z + g.x * p.y := (rfl)

/-- The action of the complex Heisenberg group on the cover is left multiplication in the group. -/
@[simp]
theorem toHeisenberg_smul (g : HeisenbergGroup ℂ) (p : Cover) :
    toHeisenberg (g • p) = g * toHeisenberg p := by
  ext <;> simp

/-- The complex Heisenberg group acts on the cover. -/
instance : MulAction (HeisenbergGroup ℂ) Cover where
  one_smul p := toHeisenberg.injective (by simp)
  mul_smul g h p := toHeisenberg.injective (by simp [mul_assoc])

/-- Each element of the complex Heisenberg group acts by an affine map, the shear by its
`x`-coordinate followed by a translation. -/
theorem smul_eq_shear_add (g : HeisenbergGroup ℂ) (p : Cover) :
    g • p = shear g.x p + mk g.x g.y g.z := by
  ext <;> simp <;> ring

/-- The complex Heisenberg group acts on the cover by holomorphic maps. -/
instance instContMDiffConstSMul {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℂ, Cover) n (HeisenbergGroup ℂ) Cover where
  contMDiff_const_smul g := by
    simp_rw [smul_eq_shear_add]
    exact (shear _).contMDiff.add contMDiff_const

/-- The differential of left multiplication by an element of the complex Heisenberg group is the
shear by its `x`-coordinate, at every point. -/
theorem mfderiv_smul (g : HeisenbergGroup ℂ) (p : Cover) :
    mfderiv 𝓘(ℂ, Cover) 𝓘(ℂ, Cover) (g • · : Cover → Cover) p = shear g.x := by
  have h : (g • · : Cover → Cover) = fun q ↦ shear g.x q + mk g.x g.y g.z :=
    funext (smul_eq_shear_add g)
  rw [h]
  exact ((shear _).hasFDerivAt.add_const _).hasMFDerivAt.mfderiv

end Cover

/-- The deck group `Γ = H(ℤ[i])` of the Iwasawa manifold: the Heisenberg group over the Gaussian
integers, acting on the cover through its inclusion into the complex Heisenberg group. -/
abbrev DeckGroup : Type := HeisenbergGroup GaussianInt

namespace Cover

/-- The deck group acts on the cover through the inclusion `H(ℤ[i]) → H(ℂ)`. -/
instance : MulAction DeckGroup Cover :=
  MulAction.compHom Cover (HeisenbergGroup.map GaussianInt.toComplex)

/-- An element of the deck group acts as its image in the complex Heisenberg group. -/
theorem deck_smul_def (γ : DeckGroup) (p : Cover) :
    γ • p = HeisenbergGroup.map GaussianInt.toComplex γ • p :=
  (rfl)

/-- The deck group acts on the cover by left multiplication in the complex Heisenberg group. -/
@[simp]
theorem toHeisenberg_deck_smul (γ : DeckGroup) (p : Cover) :
    toHeisenberg (γ • p) = HeisenbergGroup.map GaussianInt.toComplex γ * toHeisenberg p :=
  toHeisenberg_smul _ p

/-- The deck action translates the `x`-coordinate. -/
@[simp]
theorem x_deck_smul (γ : DeckGroup) (p : Cover) : (γ • p).x = γ.x + p.x := by
  simp [deck_smul_def]

/-- The deck action translates the `y`-coordinate. -/
@[simp]
theorem y_deck_smul (γ : DeckGroup) (p : Cover) : (γ • p).y = γ.y + p.y := by
  simp [deck_smul_def]

/-- The deck action shears and translates the `z`-coordinate. -/
@[simp]
theorem z_deck_smul (γ : DeckGroup) (p : Cover) :
    (γ • p).z = γ.z + p.z + γ.x * p.y := by
  simp [deck_smul_def]

/-- An element `(a, b, c)` of the deck group sends the point with coordinates `(x, y, z)` to the
point with coordinates `(a + x, b + y, c + z + a y)`. -/
@[simp]
theorem deck_smul_mk (γ : DeckGroup) (a b c : ℂ) :
    γ • mk a b c = mk (γ.x + a) (γ.y + b) (γ.z + c + γ.x * b) := by
  ext <;> simp

/-- The deck group acts on the cover by holomorphic maps. -/
instance instContMDiffConstSMulDeckGroup {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℂ, Cover) n DeckGroup Cover where
  contMDiff_const_smul γ := contMDiff_const_smul (HeisenbergGroup.map GaussianInt.toComplex γ)

/-- The deck group acts by homeomorphisms. -/
instance : ContinuousConstSMul DeckGroup Cover where
  continuous_const_smul γ := (contMDiff_const_smul (I := 𝓘(ℂ, Cover)) (n := 0) γ).continuous

/-- The deck group acts freely: two elements that move one point to the same point have the same
coordinates. -/
instance instIsCancelSMul : IsCancelSMul DeckGroup Cover where
  left_cancel' γ _ _ h := smul_left_cancel γ h
  right_cancel' γ δ p h := by
    have hx : (γ.x : ℂ) = δ.x := by simpa using congrArg x h
    have hy : (γ.y : ℂ) = δ.y := by simpa using congrArg y h
    have hz : (γ.z : ℂ) = δ.z := by
      have h' := congrArg z h
      simp only [z_deck_smul, hx] at h'
      exact add_right_cancel (add_right_cancel h')
    exact HeisenbergGroup.ext (GaussianInt.toComplex_injective hx)
      (GaussianInt.toComplex_injective hy) (GaussianInt.toComplex_injective hz)

/-- The coordinates of the elements of the deck group, as complex numbers, tend to infinity along
the cofinite filter. -/
private theorem tendsto_coords :
    Tendsto (fun γ : DeckGroup ↦ ((γ.x : ℂ), (γ.y : ℂ), (γ.z : ℂ))) cofinite
      (cocompact (ℂ × ℂ × ℂ)) := by
  have h := GaussianInt.tendsto_toComplex_cofinite_cocompact
  have hcast : Tendsto (Prod.map ((↑) : GaussianInt → ℂ) (Prod.map ((↑) : GaussianInt → ℂ)
      ((↑) : GaussianInt → ℂ))) cofinite (cocompact _) := by
    simpa only [coprod_cofinite, Filter.coprod_cocompact] using
      h.prodMap_coprod (h.prodMap_coprod h)
  refine (hcast.comp HeisenbergGroup.equivProd.injective.tendsto_cofinite).congr fun γ ↦ ?_
  simp

/-- The deck group acts properly discontinuously: only finitely many elements move a compact set
to meet another compact set. -/
instance instProperlyDiscontinuousSMul : ProperlyDiscontinuousSMul DeckGroup Cover where
  finite_disjoint_inter_image {K L} hK hL := by
    -- If `γ • p = q`, the coordinates of `γ` are a continuous function of `(q, p)`, which ranges
    -- over the compact set `L × K`.
    let c : Cover × Cover → ℂ × ℂ × ℂ := fun w ↦
      (w.1.x - w.2.x, w.1.y - w.2.y, w.1.z - w.2.z - (w.1.x - w.2.x) * w.2.y)
    have hC : IsCompact (c '' L ×ˢ K) := (hL.prod hK).image (by fun_prop)
    refine (tendsto_cofinite_cocompact_iff.mp tendsto_coords _ hC).subset fun γ hγ ↦ ?_
    obtain ⟨_, ⟨p, hp, rfl⟩, hγp⟩ := hγ
    refine ⟨(γ • p, p), ⟨hγp, hp⟩, ?_⟩
    simp only [c, x_deck_smul, y_deck_smul, z_deck_smul, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- Every orbit of the deck group meets the product of three half-open unit squares
`[0, 1) × [0, 1)` in `ℂ`. -/
theorem exists_smul_mem_reProdIm_Ico (p : Cover) :
    ∃ γ : DeckGroup, (γ • p).x ∈ Ico (0 : ℝ) 1 ×ℂ Ico 0 1 ∧
      (γ • p).y ∈ Ico (0 : ℝ) 1 ×ℂ Ico 0 1 ∧ (γ • p).z ∈ Ico (0 : ℝ) 1 ×ℂ Ico 0 1 := by
  obtain ⟨a, ha⟩ := GaussianInt.exists_sub_mem_reProdIm_Ico p.x
  obtain ⟨b, hb⟩ := GaussianInt.exists_sub_mem_reProdIm_Ico p.y
  obtain ⟨c, hc⟩ := GaussianInt.exists_sub_mem_reProdIm_Ico (p.z - a * p.y)
  refine ⟨⟨-a, -b, -c⟩, ?_, ?_, ?_⟩
  · convert ha using 1
    simp [neg_add_eq_sub]
  · convert hb using 1
    simp [neg_add_eq_sub]
  · convert hc using 1
    simp
    ring

end Cover

end IwasawaManifold

/-- The **Iwasawa manifold** `H(ℤ[i]) \ H(ℂ)`: the orbit space of the action of the deck group
`H(ℤ[i])` on `ℂ³` by `(a, b, c) • (x, y, z) = (a + x, b + y, c + z + a y)`. It is a compact
complex manifold modelled on `ℂ³`. -/
abbrev IwasawaManifold : Type :=
  MulAction.orbitRel.Quotient IwasawaManifold.DeckGroup IwasawaManifold.Cover

namespace IwasawaManifold

open Cover

/-- The projection from the cover to the Iwasawa manifold, the orbit projection. -/
abbrev mk : Cover → IwasawaManifold := Quotient.mk _

/-- Every point of the Iwasawa manifold is the image of a point of the cover. -/
theorem mk_surjective : Function.Surjective mk := Quotient.mk_surjective

/-- Two points of the cover have the same image exactly when they lie in one orbit of the deck
group. -/
theorem mk_eq_mk_iff {p q : Cover} : mk p = mk q ↔ ∃ γ : DeckGroup, γ • q = p := by
  rw [mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- The projection from the cover is a local biholomorphism, for every order of smoothness. -/
theorem isLocalDiffeomorph_mk {n : ℕ∞ω} : IsLocalDiffeomorph 𝓘(ℂ, Cover) 𝓘(ℂ, Cover) n mk :=
  isLocalDiffeomorph_quotientMk

/-- The projection from the cover is holomorphic. -/
theorem mdifferentiable_mk : MDifferentiable 𝓘(ℂ, Cover) 𝓘(ℂ, Cover) mk :=
  (isLocalDiffeomorph_mk (n := 1)).contMDiff.mdifferentiable one_ne_zero

/-- The projection from the cover is continuous. -/
theorem continuous_mk : Continuous mk := continuous_quot_mk

/-- The Iwasawa manifold is second countable. -/
instance : SecondCountableTopology IwasawaManifold :=
  ContinuousConstSMul.secondCountableTopology

/-- The Iwasawa manifold is compact: it is the image of the product of three closed unit
squares. -/
instance instCompactSpace : CompactSpace IwasawaManifold := by
  let S : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc 0 1
  have hS : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  let B : Set Cover := toProd ⁻¹' (S ×ˢ S ×ˢ S)
  have hB : IsCompact B := toProd.toHomeomorph.isCompact_preimage.2 (hS.prod (hS.prod hS))
  have hsub : Ico (0 : ℝ) 1 ×ℂ Ico 0 1 ⊆ S :=
    Complex.reProdIm_subset_iff'.2 (Or.inl ⟨Ico_subset_Icc_self, Ico_subset_Icc_self⟩)
  refine ⟨(hB.image continuous_mk).of_isClosed_subset isClosed_univ fun w _ ↦ ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective w
  obtain ⟨γ, hx, hy, hz⟩ := exists_smul_mem_reProdIm_Ico p
  exact ⟨γ • p, ⟨hsub hx, hsub hy, hsub hz⟩, MulAction.orbitRel.Quotient.quotient_smul_eq⟩

end IwasawaManifold

end TauCeti
