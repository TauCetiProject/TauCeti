/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Instances.ZMultiples
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg

/-!
# The Kodaira–Thurston manifold

The **Kodaira–Thurston manifold** is the product `(H(ℤ) \ H(ℝ)) × S¹` of the Heisenberg
nilmanifold with a circle. Here `H(R)` is the Heisenberg group `TauCeti.HeisenbergGroup R`, with
product `(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`, and `H(ℤ)` acts on `H(ℝ)` by left
multiplication. This file constructs it as a single quotient of `ℝ⁴`: the cover
`TauCeti.KodairaThurston.Cover`, with coordinates `(x, y, z, t)`, carries the action of the deck
group `Γ = H(ℤ) × ℤ` (`TauCeti.KodairaThurston.DeckGroup`) by

`((a, b, c), n) • (x, y, z, t) = (a + x, b + y, c + z + a y, n + t)`,

left multiplication on the first three coordinates and translation on the last. The action is
free and properly discontinuous, and each element acts by an affine map, whose linear part is the
shear `(x, y, z, t) ↦ (x, y, z + a y, t)` (`TauCeti.KodairaThurston.Cover.shear`). So
`TauCeti.instIsManifoldQuotient` makes the orbit space `TauCeti.KodairaThurston` an analytic
manifold modelled on `ℝ⁴`, and the projection `TauCeti.KodairaThurston.mk` is an analytic local
diffeomorphism. The orbit space is Hausdorff, second countable and compact: every orbit meets the
half-open unit cube (`TauCeti.KodairaThurston.Cover.exists_smul_mem_Ico`).

Thurston used this manifold as the first example of a compact symplectic manifold admitting no
Kähler structure; its symplectic form is constructed in
`TauCeti.Geometry.Symplectic.Manifold.KodairaThurston`.

## Main definitions

* `TauCeti.KodairaThurston.Cover`: the cover `ℝ⁴`, with coordinates `x`, `y`, `z`, `t`.
* `TauCeti.KodairaThurston.DeckGroup`: the deck group `H(ℤ) × ℤ`, acting on the cover.
* `TauCeti.KodairaThurston`: the Kodaira–Thurston manifold, the orbit space of the deck group.
* `TauCeti.KodairaThurston.mk`: the projection from the cover.

## Main results

* `TauCeti.KodairaThurston.Cover.instProperlyDiscontinuousSMul`,
  `TauCeti.KodairaThurston.Cover.instIsCancelSMul`,
  `TauCeti.KodairaThurston.Cover.instContMDiffConstSMul`: the deck group acts properly
  discontinuously and freely, by analytic maps.
* `TauCeti.KodairaThurston.Cover.smul_eq_shear_add`,
  `TauCeti.KodairaThurston.Cover.mfderiv_smul`: each element acts by an affine map with linear
  part a shear, which is therefore its differential at every point.
* `TauCeti.KodairaThurston.isLocalDiffeomorph_mk`: the projection is a local diffeomorphism.
* `TauCeti.KodairaThurston.mk_eq_mk_iff`: its fibres are the orbits of the deck group.
* `TauCeti.KodairaThurston.instCompactSpace`: the Kodaira–Thurston manifold is compact.

## References

* W. P. Thurston, *Some simple examples of symplectic manifolds*, Proceedings of the American
  Mathematical Society 55 (1976), 467–468.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace KodairaThurston

/-- The covering space `ℝ⁴` of the Kodaira–Thurston manifold, with coordinates `(x, y, z, t)`: a
type synonym of `ℝ × ℝ × ℝ × ℝ` carrying the action of the deck group
`TauCeti.KodairaThurston.DeckGroup`. -/
def Cover : Type := ℝ × ℝ × ℝ × ℝ

namespace Cover

instance : NormedAddCommGroup Cover := inferInstanceAs (NormedAddCommGroup (ℝ × ℝ × ℝ × ℝ))

instance : NormedSpace ℝ Cover := inferInstanceAs (NormedSpace ℝ (ℝ × ℝ × ℝ × ℝ))

instance : FiniteDimensional ℝ Cover := inferInstanceAs (FiniteDimensional ℝ (ℝ × ℝ × ℝ × ℝ))

/-- The coordinates `(x, y, z, t)` of a point of the cover, as a linear equivalence with
`ℝ × ℝ × ℝ × ℝ`. -/
def toProd : Cover ≃L[ℝ] ℝ × ℝ × ℝ × ℝ := ContinuousLinearEquiv.refl ℝ _

/-- The cover is four-dimensional. -/
@[simp]
theorem finrank_eq : Module.finrank ℝ Cover = 4 := by
  rw [toProd.toLinearEquiv.finrank_eq]
  simp

/-- The point of the cover with coordinates `(x, y, z, t)`. -/
def mk (x y z t : ℝ) : Cover := toProd.symm (x, y, z, t)

/-- The `x`-coordinate of a point of the cover. -/
def x (p : Cover) : ℝ := (toProd p).1

/-- The `y`-coordinate of a point of the cover. -/
def y (p : Cover) : ℝ := (toProd p).2.1

/-- The `z`-coordinate of a point of the cover. -/
def z (p : Cover) : ℝ := (toProd p).2.2.1

/-- The `t`-coordinate of a point of the cover. -/
def t (p : Cover) : ℝ := (toProd p).2.2.2

/-- The product representation of a point consists of its four coordinates. -/
@[simp]
theorem toProd_apply (p : Cover) : toProd p = (p.x, p.y, p.z, p.t) := (rfl)

/-- The inverse product representation constructs a point from its coordinates. -/
@[simp]
theorem toProd_symm_apply (a b c d : ℝ) : toProd.symm (a, b, c, d) = mk a b c d := (rfl)

@[simp] theorem x_mk (a b c d : ℝ) : (mk a b c d).x = a := (rfl)

@[simp] theorem y_mk (a b c d : ℝ) : (mk a b c d).y = b := (rfl)

@[simp] theorem z_mk (a b c d : ℝ) : (mk a b c d).z = c := (rfl)

@[simp] theorem t_mk (a b c d : ℝ) : (mk a b c d).t = d := (rfl)

/-- A point of the cover is determined by its coordinates. -/
@[ext]
theorem ext {p q : Cover} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) (ht : p.t = q.t) :
    p = q :=
  toProd.injective (Prod.ext hx (Prod.ext hy (Prod.ext hz ht)))

@[simp] theorem mk_x_y_z_t (p : Cover) : mk p.x p.y p.z p.t = p := (rfl)

@[simp] theorem x_add (p q : Cover) : (p + q).x = p.x + q.x := (rfl)

@[simp] theorem y_add (p q : Cover) : (p + q).y = p.y + q.y := (rfl)

@[simp] theorem z_add (p q : Cover) : (p + q).z = p.z + q.z := (rfl)

@[simp] theorem t_add (p q : Cover) : (p + q).t = p.t + q.t := (rfl)

@[simp] theorem x_neg (p : Cover) : (-p).x = -p.x := (rfl)

@[simp] theorem y_neg (p : Cover) : (-p).y = -p.y := (rfl)

@[simp] theorem z_neg (p : Cover) : (-p).z = -p.z := (rfl)

@[simp] theorem t_neg (p : Cover) : (-p).t = -p.t := (rfl)

@[simp] theorem x_sub (p q : Cover) : (p - q).x = p.x - q.x := (rfl)

@[simp] theorem y_sub (p q : Cover) : (p - q).y = p.y - q.y := (rfl)

@[simp] theorem z_sub (p q : Cover) : (p - q).z = p.z - q.z := (rfl)

@[simp] theorem t_sub (p q : Cover) : (p - q).t = p.t - q.t := (rfl)

@[simp] theorem x_zero : (0 : Cover).x = 0 := (rfl)

@[simp] theorem y_zero : (0 : Cover).y = 0 := (rfl)

@[simp] theorem z_zero : (0 : Cover).z = 0 := (rfl)

@[simp] theorem t_zero : (0 : Cover).t = 0 := (rfl)

@[simp] theorem x_smul (c : ℝ) (p : Cover) : (c • p).x = c * p.x := (rfl)

@[simp] theorem y_smul (c : ℝ) (p : Cover) : (c • p).y = c * p.y := (rfl)

@[simp] theorem z_smul (c : ℝ) (p : Cover) : (c • p).z = c * p.z := (rfl)

@[simp] theorem t_smul (c : ℝ) (p : Cover) : (c • p).t = c * p.t := (rfl)

/-- The `x`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_x : Continuous x := continuous_fst.comp toProd.continuous

/-- The `y`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_y : Continuous y := continuous_snd.fst.comp toProd.continuous

/-- The `z`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_z : Continuous z := continuous_snd.snd.fst.comp toProd.continuous

/-- The `t`-coordinate is continuous. -/
@[fun_prop]
theorem continuous_t : Continuous t := continuous_snd.snd.snd.comp toProd.continuous

/-- The shear `(x, y, z, t) ↦ (x, y, z + a y, t)`, the linear part of the action of an element of
the deck group whose first Heisenberg coordinate is `a`. -/
def shear (a : ℝ) : Cover →L[ℝ] Cover :=
  LinearMap.toContinuousLinearMap
    { toFun p := mk p.x p.y (p.z + a * p.y) p.t
      map_add' p q := by
        ext <;> simp only [x_mk, y_mk, z_mk, t_mk, x_add, y_add, z_add, t_add]; ring
      map_smul' c p := by
        ext <;> simp only [x_mk, y_mk, z_mk, t_mk, x_smul, y_smul, z_smul, t_smul,
          RingHom.id_apply]; ring }

/-- The shear in coordinates. -/
@[simp]
theorem shear_apply (a : ℝ) (p : Cover) : shear a p = mk p.x p.y (p.z + a * p.y) p.t := (rfl)

end Cover

/-- The deck group `Γ = H(ℤ) × ℤ` of the Kodaira–Thurston manifold: the integer Heisenberg group,
acting on the first three coordinates of the cover by left multiplication, times the integers,
acting on the last coordinate by translation. -/
abbrev DeckGroup : Type := HeisenbergGroup ℤ × Multiplicative ℤ

namespace Cover

instance : SMul DeckGroup Cover where
  smul γ p := mk (γ.1.x + p.x) (γ.1.y + p.y) (γ.1.z + p.z + γ.1.x * p.y) (γ.2.toAdd + p.t)

/-- An element `((a, b, c), n)` of the deck group acts by
`(x, y, z, t) ↦ (a + x, b + y, c + z + a y, n + t)`. -/
theorem smul_def (γ : DeckGroup) (p : Cover) :
    γ • p = mk (γ.1.x + p.x) (γ.1.y + p.y) (γ.1.z + p.z + γ.1.x * p.y) (γ.2.toAdd + p.t) :=
  (rfl)

/-- An element `((a, b, c), n)` of the deck group acts by
`(x, y, z, t) ↦ (a + x, b + y, c + z + a y, n + t)`. -/
@[simp]
theorem smul_mk (γ : DeckGroup) (x y z t : ℝ) :
    γ • mk x y z t = mk (γ.1.x + x) (γ.1.y + y) (γ.1.z + z + γ.1.x * y) (γ.2.toAdd + t) :=
  (rfl)

/-- The deck action translates the `x`-coordinate. -/
@[simp]
theorem x_deck_smul (γ : DeckGroup) (p : Cover) : (γ • p).x = γ.1.x + p.x := (rfl)

/-- The deck action translates the `y`-coordinate. -/
@[simp]
theorem y_deck_smul (γ : DeckGroup) (p : Cover) : (γ • p).y = γ.1.y + p.y := (rfl)

/-- The deck action shears and translates the `z`-coordinate. -/
@[simp]
theorem z_deck_smul (γ : DeckGroup) (p : Cover) :
    (γ • p).z = γ.1.z + p.z + γ.1.x * p.y := (rfl)

/-- The deck action translates the `t`-coordinate. -/
@[simp]
theorem t_deck_smul (γ : DeckGroup) (p : Cover) : (γ • p).t = γ.2.toAdd + p.t := (rfl)

/-- The deck group acts on the cover. -/
instance : MulAction DeckGroup Cover where
  one_smul p := by ext <;> simp [smul_def]
  mul_smul γ δ p := by
    ext <;> simp only [smul_def, x_mk, y_mk, z_mk, t_mk, Prod.fst_mul, Prod.snd_mul,
      HeisenbergGroup.mul_x, HeisenbergGroup.mul_y, HeisenbergGroup.mul_z, toAdd_mul,
      Int.cast_add, Int.cast_mul] <;> ring

/-- Each element of the deck group acts by an affine map, the shear by its first Heisenberg
coordinate followed by a translation. -/
theorem smul_eq_shear_add (γ : DeckGroup) (p : Cover) :
    γ • p = shear γ.1.x p + mk γ.1.x γ.1.y γ.1.z γ.2.toAdd := by
  ext <;> simp [smul_def] <;> ring

/-- The deck group acts by analytic maps. -/
instance instContMDiffConstSMul {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, Cover) n DeckGroup Cover where
  contMDiff_const_smul γ := by
    simp_rw [smul_eq_shear_add]
    exact (shear _).contMDiff.add contMDiff_const

/-- The differential of the action of an element of the deck group is the shear by its first
Heisenberg coordinate, at every point. -/
theorem mfderiv_smul (γ : DeckGroup) (p : Cover) :
    mfderiv 𝓘(ℝ, Cover) 𝓘(ℝ, Cover) (γ • · : Cover → Cover) p = shear γ.1.x := by
  have h : (γ • · : Cover → Cover) = fun q ↦ shear γ.1.x q + mk γ.1.x γ.1.y γ.1.z γ.2.toAdd :=
    funext (smul_eq_shear_add γ)
  rw [h]
  exact ((shear _).hasFDerivAt.add_const _).hasMFDerivAt.mfderiv

/-- The deck group acts by homeomorphisms. -/
instance : ContinuousConstSMul DeckGroup Cover where
  continuous_const_smul γ := (contMDiff_const_smul (I := 𝓘(ℝ, Cover)) (n := 0) γ).continuous

/-- The deck group acts freely: two elements that move one point to the same point have the same
coordinates. -/
instance instIsCancelSMul : IsCancelSMul DeckGroup Cover where
  left_cancel' γ _ _ h := smul_left_cancel γ h
  right_cancel' γ δ p h := by
    have hx : (γ.1.x : ℝ) = δ.1.x := by simpa [smul_def] using congrArg x h
    have hy : (γ.1.y : ℝ) = δ.1.y := by simpa [smul_def] using congrArg y h
    have ht : (γ.2.toAdd : ℝ) = δ.2.toAdd := by simpa [smul_def] using congrArg t h
    have hz : (γ.1.z : ℝ) = δ.1.z := by
      have h' := congrArg z h
      simp only [smul_def, z_mk] at h'
      rw [hx] at h'
      linarith
    exact Prod.ext (HeisenbergGroup.ext (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by exact_mod_cast hz)) (Multiplicative.toAdd.injective (by exact_mod_cast ht))

/-- The integer coordinates of the elements of the deck group, as real numbers, tend to infinity
along the cofinite filter. -/
private theorem tendsto_coords :
    Tendsto (fun γ : DeckGroup ↦ ((γ.1.x : ℝ), (γ.1.y : ℝ), (γ.1.z : ℝ), (γ.2.toAdd : ℝ)))
      cofinite (cocompact (ℝ × ℝ × ℝ × ℝ)) := by
  have hcast : Tendsto (Prod.map (Int.cast : ℤ → ℝ) (Prod.map (Int.cast : ℤ → ℝ)
      (Prod.map (Int.cast : ℤ → ℝ) (Int.cast : ℤ → ℝ)))) cofinite (cocompact _) := by
    simpa only [coprod_cofinite, Filter.coprod_cocompact] using
      Int.tendsto_coe_cofinite.prodMap_coprod (Int.tendsto_coe_cofinite.prodMap_coprod
        (Int.tendsto_coe_cofinite.prodMap_coprod Int.tendsto_coe_cofinite))
  have hinj : Function.Injective fun γ : DeckGroup ↦ (γ.1.x, γ.1.y, γ.1.z, γ.2.toAdd) := by
    intro γ δ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (HeisenbergGroup.ext h.1 h.2.1 h.2.2.1) (Multiplicative.toAdd.injective h.2.2.2)
  exact hcast.comp hinj.tendsto_cofinite

/-- The deck group acts properly discontinuously: only finitely many elements move a compact set
to meet another compact set. -/
instance instProperlyDiscontinuousSMul : ProperlyDiscontinuousSMul DeckGroup Cover where
  finite_disjoint_inter_image {K L} hK hL := by
    -- If `γ • p = q`, the integer coordinates of `γ` are a continuous function of `(q, p)`, which
    -- ranges over the compact set `L × K`.
    let c : Cover × Cover → ℝ × ℝ × ℝ × ℝ := fun w ↦
      (w.1.x - w.2.x, w.1.y - w.2.y, w.1.z - w.2.z - (w.1.x - w.2.x) * w.2.y, w.1.t - w.2.t)
    have hC : IsCompact (c '' L ×ˢ K) := (hL.prod hK).image (by fun_prop)
    refine (tendsto_cofinite_cocompact_iff.mp tendsto_coords _ hC).subset fun γ hγ ↦ ?_
    obtain ⟨_, ⟨p, hp, rfl⟩, hγp⟩ := hγ
    refine ⟨(γ • p, p), ⟨hγp, hp⟩, ?_⟩
    simp only [c, smul_def, x_mk, y_mk, z_mk, t_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- Every orbit of the deck group meets the half-open unit cube `[0, 1)⁴`. -/
theorem exists_smul_mem_Ico (p : Cover) :
    ∃ γ : DeckGroup, (γ • p).x ∈ Ico 0 1 ∧ (γ • p).y ∈ Ico 0 1 ∧ (γ • p).z ∈ Ico 0 1 ∧
      (γ • p).t ∈ Ico 0 1 := by
  refine ⟨(⟨-⌊p.x⌋, -⌊p.y⌋, -⌊p.z - ⌊p.x⌋ * p.y⌋⟩, Multiplicative.ofAdd (-⌊p.t⌋)), ?_⟩
  have h : ∀ r : ℝ, r - ⌊r⌋ ∈ Ico (0 : ℝ) 1 := fun r ↦
    ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩
  simp only [smul_def, x_mk, y_mk, z_mk, t_mk, toAdd_ofAdd, Int.cast_neg]
  refine ⟨by simpa [neg_add_eq_sub] using h p.x, by simpa [neg_add_eq_sub] using h p.y, ?_,
    by simpa [neg_add_eq_sub] using h p.t⟩
  convert h (p.z - ⌊p.x⌋ * p.y) using 1
  ring

end Cover

end KodairaThurston

/-- The **Kodaira–Thurston manifold** `(H(ℤ) \ H(ℝ)) × S¹`: the orbit space of the action of the
deck group `H(ℤ) × ℤ` on `ℝ⁴` by
`((a, b, c), n) • (x, y, z, t) = (a + x, b + y, c + z + a y, n + t)`. It is a compact analytic
manifold modelled on `ℝ⁴`. -/
abbrev KodairaThurston : Type :=
  MulAction.orbitRel.Quotient KodairaThurston.DeckGroup KodairaThurston.Cover

namespace KodairaThurston

open Cover

/-- The projection from the cover to the Kodaira–Thurston manifold, the orbit projection. -/
abbrev mk : Cover → KodairaThurston := Quotient.mk _

/-- Every point of the Kodaira–Thurston manifold is the image of a point of the cover. -/
theorem mk_surjective : Function.Surjective mk := Quotient.mk_surjective

/-- Two points of the cover have the same image exactly when they lie in one orbit of the deck
group. -/
theorem mk_eq_mk_iff {p q : Cover} : mk p = mk q ↔ ∃ γ : DeckGroup, γ • q = p := by
  rw [mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- The projection from the cover is a local diffeomorphism, for every order of smoothness. -/
theorem isLocalDiffeomorph_mk {n : ℕ∞ω} : IsLocalDiffeomorph 𝓘(ℝ, Cover) 𝓘(ℝ, Cover) n mk :=
  isLocalDiffeomorph_quotientMk

/-- The projection from the cover is continuous. -/
theorem continuous_mk : Continuous mk := continuous_quot_mk

/-- The Kodaira–Thurston manifold is second countable. -/
instance : SecondCountableTopology KodairaThurston :=
  ContinuousConstSMul.secondCountableTopology

/-- The Kodaira–Thurston manifold is compact: it is the image of the closed unit cube. -/
instance instCompactSpace : CompactSpace KodairaThurston := by
  let B : Set Cover := toProd ⁻¹' (Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1)
  have hB : IsCompact B := toProd.toHomeomorph.isCompact_preimage.2
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))
  refine ⟨(hB.image continuous_mk).of_isClosed_subset isClosed_univ fun w _ ↦ ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective w
  obtain ⟨γ, hx, hy, hz, ht⟩ := exists_smul_mem_Ico p
  exact ⟨γ • p, ⟨Ico_subset_Icc_self hx, Ico_subset_Icc_self hy, Ico_subset_Icc_self hz,
    Ico_subset_Icc_self ht⟩, MulAction.orbitRel.Quotient.quotient_smul_eq⟩

end KodairaThurston

end TauCeti
