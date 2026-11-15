/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RiemannSurface.FiberMultiset
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
import Mathlib.Geometry.Manifold.Complex

/-!
# Compact curves in a flat line bundle over a complex torus

Let `L` be a discrete subgroup of `ℂ`, for instance a lattice, so that `ℂ / L` is a complex
torus, and let `ψ : L → ℂˣ` be a character, given as an additive character `ψ : AddChar L ℂ`.
The **flat line** of `ψ` over `ℂ / L` is the quotient of `ℂ × ℂ` by the action
`γ +ᵥ (z, v) = (γ + z, ψ(γ) v)` of `L` (`TauCeti.FlatLine L ψ`). It is a complex surface, the total
space of the holomorphic line bundle over `ℂ / L` with holonomy `ψ`, and the projection
`[z, v] ↦ [z]` (`TauCeti.FlatLine.proj`) is holomorphic. Its holomorphic sections over `ℂ / L` are
the entire functions `f` with `f (z + γ) = ψ(γ) f(z)`, and those of its `j`-th power the ones with
`f (z + γ) = ψ(γ)ʲ f(z)`. A point over `[z]` has a coordinate in the frame at `z`
(`TauCeti.FlatLine.fiberCoord`): `[z, v]` has coordinate `v`, and the frames at `z` and `γ + z`
differ by `ψ(γ)`.

The main result is that compact holomorphic curves in the total space lie in the zero section as
soon as the first few powers of the flat line have no nonzero holomorphic sections
(`TauCeti.FlatLine.range_subset_range_zeroSection`): if `u` is a nonconstant holomorphic map from a
compact connected Riemann surface `S` to the flat line whose projection to `ℂ / L` has degree `m`,
and the powers `1, …, m` of the flat line have no nonzero holomorphic section, then `u` takes
values in the zero section. When `L` is a lattice and `ψ` is unitary, a holomorphic section of the
`j`-th power has `L`-periodic modulus, hence is bounded and constant by Liouville's theorem, so the
hypothesis holds as soon as `ψʲ` is nontrivial for `1 ≤ j ≤ m`, for instance when some `ψ(γ)` is
not a root of unity.

The proof is the symmetric-function argument. The projection `p = proj ∘ u` is nonconstant,
since a holomorphic map from `S` into a single fibre `ℂ` is constant, so `p` is a finite
holomorphic map of some degree `m`. Over `[z]` the fibre of `p`, counted with multiplicity
(`TauCeti.RiemannSurface.fiberMultiset`), has `m` points, and the coordinates of their images in
the frame at `z` are the roots of a monic polynomial `Wᵐ - b₁(z) Wᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ(z)`. The
coefficients `bⱼ` are the elementary symmetric functions of these coordinates, so they are entire
(`TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`, which holds across the branch
values of `p`), and changing the frame by `ψ(γ)` multiplies `bⱼ` by `ψ(γ)ʲ`: each `bⱼ` is a
holomorphic section of the `j`-th power. By hypothesis they all vanish, so every coordinate is a
root of `Wᵐ` and lies in the zero section.

In Taubes's comparison of Seiberg–Witten and Gromov invariants, an embedded square-zero torus is
given a flat normal model with holonomy of infinite order, and this theorem shows that the only
compact curves in that model are covers of the torus itself, the zero section. No hypothesis on
the genus of `S`, on the ramification of `p` or on the multiplicity of the curve is needed.

## Main definitions

* `TauCeti.FlatLine L ψ`: the total space of the flat line of `ψ` over `ℂ / L`.
* `TauCeti.FlatLine.mk L ψ z v`: the class of `(z, v)`.
* `TauCeti.FlatLine.proj`, `TauCeti.FlatLine.zeroSection`: the projection to `ℂ / L` and the zero
  section.
* `TauCeti.FlatLine.fiberCoord z`: the coordinate of the points over `[z]` in the frame at `z`.

## Main results

* `TauCeti.FlatLine.mk_eq_mk_iff`: two pairs have the same class exactly when they differ by the
  action of `L`.
* `TauCeti.FlatLine.isLocalDiffeomorph_mk`, `TauCeti.FlatLine.contMDiff_proj`: the quotient map
  is a local biholomorphism and the projection is holomorphic.
* `TauCeti.FlatLine.range_subset_range_zeroSection`: compact curves lie in the zero section.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8, for the elementary symmetric functions of the values of a function along the fibres of a
  branched covering.
-/

public section

open Set Filter Function Topology
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable (L : Submodule ℤ ℂ) (ψ : AddChar L ℂ)

namespace FlatLine

/-- The space `ℂ × ℂ` with the action `γ +ᵥ (z, v) = (γ + z, ψ(γ) v)` of the lattice `L`, whose
orbit space is the flat line of `ψ`. -/
@[expose]
def Cover (_L : Submodule ℤ ℂ) (_ψ : AddChar _L ℂ) : Type := ℂ × ℂ

instance : TopologicalSpace (Cover L ψ) := inferInstanceAs (TopologicalSpace (ℂ × ℂ))

instance : T2Space (Cover L ψ) := inferInstanceAs (T2Space (ℂ × ℂ))

instance : LocallyCompactSpace (Cover L ψ) := inferInstanceAs (LocallyCompactSpace (ℂ × ℂ))

instance : ChartedSpace (ℂ × ℂ) (Cover L ψ) := inferInstanceAs (ChartedSpace (ℂ × ℂ) (ℂ × ℂ))

instance {n : ℕ∞ω} : IsManifold 𝓘(ℂ, ℂ × ℂ) n (Cover L ψ) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, ℂ × ℂ) n (ℂ × ℂ))

/-- The pair `(z, v)` as a point of `TauCeti.FlatLine.Cover L ψ`. -/
@[expose] def Cover.mk (z v : ℂ) : Cover L ψ := (z, v)

instance : AddAction L (Cover L ψ) where
  vadd γ x := ((γ : ℂ) + x.1, ψ γ * x.2)
  zero_vadd x := by
    -- Unfold the action just defined.
    change (((0 : L) : ℂ) + x.1, ψ 0 * x.2) = x
    rw [ZeroMemClass.coe_zero, zero_add, AddChar.map_zero_eq_one, one_mul]
    rfl
  add_vadd γ γ' x := by
    -- Unfold the action just defined.
    change (((γ + γ' : L) : ℂ) + x.1, ψ (γ + γ') * x.2) = ((γ : ℂ) + ((γ' : ℂ) + x.1),
      ψ γ * (ψ γ' * x.2))
    rw [Submodule.coe_add, add_assoc, AddChar.map_add_eq_mul, mul_assoc]

variable {L ψ}

@[simp]
theorem vadd_mk (γ : L) (z v : ℂ) :
    γ +ᵥ Cover.mk L ψ z v = Cover.mk L ψ ((γ : ℂ) + z) (ψ γ * v) :=
  rfl

variable (L ψ)

instance : IsCancelVAdd L (Cover L ψ) where
  left_cancel' γ x y h := by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (add_left_cancel h₁) (mul_left_cancel₀ (ψ.val_isUnit γ).ne_zero h₂)
  right_cancel' γ γ' x h := Subtype.ext (add_right_cancel (Prod.mk.inj h).1)

/-- The action of a lattice element on the cover, as a map of `ℂ × ℂ`. -/
private theorem vadd_eq (γ : L) :
    (fun x : Cover L ψ ↦ γ +ᵥ x) = fun x : ℂ × ℂ ↦ ((γ : ℂ) + x.1, ψ γ * x.2) :=
  rfl

instance : ContinuousConstVAdd L (Cover L ψ) where
  continuous_const_vadd γ := by
    rw [vadd_eq]
    fun_prop

instance {n : ℕ∞ω} : ContMDiffConstVAdd 𝓘(ℂ, ℂ × ℂ) n L (Cover L ψ) where
  contMDiff_const_vadd γ := by
    rw [vadd_eq]
    exact contMDiff_iff_contDiff.2 (by fun_prop)

instance [DiscreteTopology L] : ProperlyDiscontinuousVAdd L (Cover L ψ) where
  finite_disjoint_inter_image {K K'} hK hK' := by
    -- The first coordinate of `γ +ᵥ x` is the translate of the first coordinate of `x`.
    refine (ProperlyDiscontinuousVAdd.finite_disjoint_inter_image (Γ := L)
      (hK.image (continuous_fst (X := ℂ) (Y := ℂ)))
      (hK'.image (continuous_fst (X := ℂ) (Y := ℂ)))).subset fun γ ⟨_, ⟨x, hx, rfl⟩, hy⟩ ↦ ?_
    exact ⟨_, ⟨x.1, mem_image_of_mem Prod.fst hx, rfl⟩, mem_image_of_mem Prod.fst hy⟩

end FlatLine

/-- The **flat line** of a character `ψ` of `L`: the quotient of `ℂ × ℂ` by
`γ +ᵥ (z, v) = (γ + z, ψ(γ) v)`, the total space of the holomorphic line bundle over `ℂ / L` with
holonomy `ψ`. -/
abbrev FlatLine : Type := AddAction.orbitRel.Quotient L (FlatLine.Cover L ψ)

namespace FlatLine

/-- The class of `(z, v)` in the flat line. -/
def mk (z v : ℂ) : FlatLine L ψ := Quotient.mk _ (Cover.mk L ψ z v)

variable {L ψ}

theorem mk_eq_mk_iff {z z' v v' : ℂ} :
    mk L ψ z v = mk L ψ z' v' ↔ ∃ γ : L, (γ : ℂ) + z' = z ∧ ψ γ * v' = v := by
  rw [mk, mk, Quotient.eq, AddAction.orbitRel_apply]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, (Prod.mk.inj hγ).1, (Prod.mk.inj hγ).2⟩
  · rintro ⟨γ, h₁, h₂⟩
    exact ⟨γ, Prod.ext h₁ h₂⟩

/-- Every class is the class of a pair. -/
theorem exists_mk_eq (n : FlatLine L ψ) : ∃ z v, mk L ψ z v = n := by
  obtain ⟨⟨z, v⟩, rfl⟩ := Quotient.exists_rep n
  exact ⟨z, v, rfl⟩

/-- Moving a pair by the action of `γ` does not change its class. -/
@[simp]
theorem mk_add_mul (γ : L) (z v : ℂ) : mk L ψ ((γ : ℂ) + z) (ψ γ * v) = mk L ψ z v :=
  mk_eq_mk_iff.2 ⟨γ, rfl, rfl⟩

variable (L ψ)

/-- The quotient map `ℂ × ℂ → FlatLine L ψ` is a local biholomorphism. -/
theorem isLocalDiffeomorph_mk [DiscreteTopology L] {n : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2 :=
  isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ, ℂ × ℂ)) (n := n) (G := L) (M := Cover L ψ)

theorem surjective_mk : Surjective fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2 := fun n ↦
  let ⟨z, v, h⟩ := exists_mk_eq n
  ⟨(z, v), h⟩

/-- The **projection** of the flat line to `ℂ / L`, `[z, v] ↦ [z]`. -/
def proj : FlatLine L ψ → AddAction.orbitRel.Quotient L ℂ :=
  Quotient.map' (fun x : Cover L ψ ↦ x.1) fun _ _ ⟨γ, h⟩ ↦ ⟨γ, congrArg Prod.fst h⟩

/-- The **zero section** of the flat line, `[z] ↦ [z, 0]`. -/
def zeroSection : AddAction.orbitRel.Quotient L ℂ → FlatLine L ψ :=
  Quotient.map' (Cover.mk L ψ · 0) fun _ z' ⟨γ, h⟩ ↦
    ⟨γ, (vadd_mk γ z' 0).trans (by rw [mul_zero, ← h]; rfl)⟩

variable {L ψ}

@[simp]
theorem proj_mk (z v : ℂ) :
    proj L ψ (mk L ψ z v) = Quotient.mk (AddAction.orbitRel L ℂ) z :=
  (rfl)

@[simp]
theorem zeroSection_mk (z : ℂ) :
    zeroSection L ψ (Quotient.mk (AddAction.orbitRel L ℂ) z) = mk L ψ z 0 :=
  (rfl)

@[simp]
theorem proj_zeroSection (x : AddAction.orbitRel.Quotient L ℂ) :
    proj L ψ (zeroSection L ψ x) = x := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep x
  rfl

/-- A pair lies over `[z]` exactly when its first coordinate is a translate of `z`. -/
theorem proj_mk_eq_iff {z z' v : ℂ} :
    proj L ψ (mk L ψ z' v) = Quotient.mk (AddAction.orbitRel L ℂ) z ↔
      ∃ γ : L, (γ : ℂ) + z' = z := by
  rw [proj_mk, Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  refine ⟨fun ⟨γ, h⟩ ↦ ⟨-γ, ?_⟩, fun ⟨γ, h⟩ ↦ ⟨-γ, ?_⟩⟩ <;>
    rw [← h, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, neg_add_cancel_left]

variable (L ψ) in
/-- The projection of the flat line to `ℂ / L` is holomorphic. -/
theorem contMDiff_proj [DiscreteTopology L] {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) n (proj L ψ) := by
  rw [← (isLocalDiffeomorph_mk L ψ (n := n)).contMDiff_comp_iff (surjective_mk L ψ) le_rfl]
  exact (isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := n) (G := L) (M := ℂ)).contMDiff.comp
    (contMDiff_iff_contDiff.2 contDiff_fst)

variable (L ψ) in
/-- The zero section of the flat line is holomorphic. -/
theorem contMDiff_zeroSection [DiscreteTopology L] {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) n (zeroSection L ψ) := by
  rw [← (isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := n) (G := L) (M := ℂ)).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl]
  exact (isLocalDiffeomorph_mk L ψ (n := n)).contMDiff.comp
    (contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const))

/-! ### The coordinate in a frame -/

open Classical in
variable (L ψ) in
/-- The **coordinate in the frame at `z`** of a point of the flat line: `v` for the class
`[z, v]`. It is only meaningful over `[z]`, and is `0` elsewhere. -/
def fiberCoord (z : ℂ) (n : FlatLine L ψ) : ℂ :=
  if h : ∃ v, mk L ψ z v = n then h.choose else 0

@[simp]
theorem fiberCoord_mk_self (z v : ℂ) : fiberCoord L ψ z (mk L ψ z v) = v := by
  have h : ∃ v', mk L ψ z v' = mk L ψ z v := ⟨v, rfl⟩
  simp only [fiberCoord, h, ↓reduceDIte]
  obtain ⟨γ, hγ, hv⟩ := mk_eq_mk_iff.1 h.choose_spec
  rw [add_eq_right, ZeroMemClass.coe_eq_zero] at hγ
  rw [← hv, hγ, AddChar.map_zero_eq_one, one_mul]

/-- Changing the frame from `z` to `γ + z` multiplies the coordinate by `ψ(γ)`. -/
theorem fiberCoord_add (γ : L) (z : ℂ) (n : FlatLine L ψ) :
    fiberCoord L ψ ((γ : ℂ) + z) n = ψ γ * fiberCoord L ψ z n := by
  by_cases h : ∃ v, mk L ψ z v = n
  · obtain ⟨v, rfl⟩ := h
    rw [← mk_add_mul γ z v, fiberCoord_mk_self, mk_add_mul, fiberCoord_mk_self]
  · have h' : ¬ ∃ v, mk L ψ ((γ : ℂ) + z) v = n := fun ⟨v, hv⟩ ↦ h ⟨ψ (-γ) * v, by
      rw [← hv, ← mk_add_mul γ z, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one, one_mul]⟩
    simp only [fiberCoord, h, h', ↓reduceDIte, mul_zero]

/-- A point over `[z]` is the class of `z` and its coordinate in the frame at `z`. -/
theorem mk_fiberCoord {z : ℂ} {n : FlatLine L ψ}
    (hn : proj L ψ n = Quotient.mk (AddAction.orbitRel L ℂ) z) :
    mk L ψ z (fiberCoord L ψ z n) = n := by
  obtain ⟨z', v, rfl⟩ := exists_mk_eq n
  obtain ⟨γ, rfl⟩ := proj_mk_eq_iff.1 hn
  rw [← mk_add_mul γ z' v, fiberCoord_mk_self]

/-- A point lies in the zero section exactly when its coordinate in the frame at a point under it
vanishes. -/
theorem mem_range_zeroSection_iff {z : ℂ} {n : FlatLine L ψ}
    (hn : proj L ψ n = Quotient.mk (AddAction.orbitRel L ℂ) z) :
    n ∈ range (zeroSection L ψ) ↔ fiberCoord L ψ z n = 0 := by
  refine ⟨?_, fun h ↦ ⟨_, by rw [zeroSection_mk, ← h, mk_fiberCoord hn]⟩⟩
  rintro ⟨x, rfl⟩
  rw [proj_zeroSection] at hn
  rw [hn, zeroSection_mk, fiberCoord_mk_self]

/-- Near a point `z₀`, the coordinate in the frame at a point `z` of `ℂ` is read by a single
function, holomorphic near the points over `z`: a local section of `ℂ → ℂ / L` chooses the frame. -/
private theorem exists_local_fiberCoord [DiscreteTopology L] (z₀ : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ F : FlatLine L ψ → ℂ,
      (∀ z ∈ U, ∀ v, F (mk L ψ z v) = v) ∧
      ∀ z ∈ U, ∀ v, MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) F (mk L ψ z v) := by
  have hq := isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := 1) (G := L) (M := ℂ) z₀
  obtain ⟨U, hU, hUo, hz₀⟩ := eventually_nhds_iff.1 hq.localInverse_eventuallyEq_left
  set σ := hq.localInverse
  let F : FlatLine L ψ → ℂ := fun n ↦ fiberCoord L ψ (σ (proj L ψ n)) n
  have hF : ∀ z ∈ U, ∀ v, F (mk L ψ z v) = v := fun z hz v ↦ by
    simp only [F, proj_mk]
    rw [show σ (Quotient.mk _ z) = z from hU z hz, fiberCoord_mk_self]
  refine ⟨U, hUo, hz₀, F, hF, fun z hz v ↦ ?_⟩
  -- Read through the quotient map, `F` is the second coordinate near `(z, v)`.
  have hcomp : (F ∘ fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2) =ᶠ[𝓝 (z, v)] Prod.snd :=
    Filter.mem_of_superset ((hUo.prod isOpen_univ).mem_nhds ⟨hz, mem_univ v⟩)
      fun x hx ↦ hF x.1 hx.1 x.2
  have hsnd : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (F ∘ fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2) (z, v) :=
    (mdifferentiableAt_iff_differentiableAt.2 differentiableAt_snd).congr_of_eventuallyEq hcomp
  exact ((isLocalDiffeomorph_mk L ψ (n := 1) (z, v)).mdifferentiableAt_comp_iff one_ne_zero).1
    hsnd

/-! ### Compact curves lie in the zero section -/

section Curve

variable [DiscreteTopology L] {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
  [IsManifold 𝓘(ℂ) 1 S] [CompactSpace S] [T2Space S] [ConnectedSpace S]
  {u : S → FlatLine L ψ}

omit [T2Space S] in
/-- A holomorphic map from a compact connected Riemann surface into one fibre of the flat line is
constant. -/
private theorem exists_eq_const_of_proj_eq (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u) {z₀ : ℂ}
    (h : ∀ x, proj L ψ (u x) = Quotient.mk (AddAction.orbitRel L ℂ) z₀) : ∃ n, ∀ x, u x = n := by
  obtain ⟨U, -, hz₀, F, hF, hFd⟩ := exists_local_fiberCoord (L := L) (ψ := ψ) z₀
  have huF : ∀ x, u x = mk L ψ z₀ (F (u x)) := fun x ↦ by
    rw [← mk_fiberCoord (h x), hF z₀ hz₀]
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∘ u) := fun x ↦
    MDifferentiableAt.comp x (huF x ▸ hFd z₀ hz₀ _) (hu x)
  obtain ⟨c, hc⟩ := hg.exists_eq_const_of_compactSpace
  exact ⟨mk L ψ z₀ c, fun x ↦ by rw [huF x, ← Function.comp_apply (f := F), hc,
    Function.const_apply]⟩

/-- The symmetric functions `bⱼ(z)` of the coordinates, in the frame at `z`, of the images of the
points of a fibre of the projection of a curve. -/
private abbrev fiberEsymm (u : S → FlatLine L ψ) (j : ℕ) (z : ℂ) : ℂ :=
  ((RiemannSurface.fiberMultiset (proj L ψ ∘ u) (Quotient.mk (AddAction.orbitRel L ℂ) z)).map
    fun x ↦ fiberCoord L ψ z (u x)).esymm j

omit [IsManifold 𝓘(ℂ) 1 S] [CompactSpace S] [T2Space S] [ConnectedSpace S] in
/-- Changing the frame by `γ` multiplies `bⱼ` by `ψ(γ)ʲ`: `bⱼ` is a section of the `j`-th power
of the flat line. -/
private theorem fiberEsymm_add (j : ℕ) (γ : L) (z : ℂ) :
    fiberEsymm u j (z + γ) = ψ γ ^ j * fiberEsymm u j z := by
  have hz : Quotient.mk (AddAction.orbitRel L ℂ) (z + γ) = Quotient.mk _ z :=
    Quotient.sound ⟨γ, add_comm (γ : ℂ) z⟩
  simp only [fiberEsymm]
  rw [hz, add_comm z]
  simp only [fiberCoord_add, Multiset.esymm_map_mul_left]

omit [ConnectedSpace S] in
/-- The symmetric functions `bⱼ` of the fibre coordinates are entire, also across the branch
values of the projection. -/
private theorem differentiable_fiberEsymm (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u)
    (hne : ∀ x, ¬ EventuallyConst (proj L ψ ∘ u) (𝓝 x)) (j : ℕ) :
    Differentiable ℂ (fiberEsymm u j) := by
  intro z₀
  set p := proj L ψ ∘ u
  have hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p :=
    ((contMDiff_proj L ψ (n := 1)).mdifferentiable one_ne_zero).comp hu
  obtain ⟨U, hUo, hz₀, F, hF, hFd⟩ := exists_local_fiberCoord (L := L) (ψ := ψ) z₀
  set y₀ := Quotient.mk (AddAction.orbitRel L ℂ) z₀
  set e' := chartAt ℂ y₀
  -- The coordinate `F ∘ u` is holomorphic near the fibre over `[z₀]`.
  have hg : ∀ x ∈ p ⁻¹' {y₀}, ∀ᶠ x' in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ u) x' := by
    intro x hx
    have hV : IsOpen ((fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2) '' (U ×ˢ univ)) :=
      (isLocalDiffeomorph_mk L ψ (n := 1)).isOpenMap _ (hUo.prod isOpen_univ)
    have hux : u x ∈ (fun x : ℂ × ℂ ↦ mk L ψ x.1 x.2) '' (U ×ˢ univ) :=
      ⟨(z₀, fiberCoord L ψ z₀ (u x)), ⟨hz₀, mem_univ _⟩, mk_fiberCoord hx⟩
    filter_upwards [hu.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hux)] with x' hx'
    obtain ⟨⟨z, v⟩, ⟨hz, -⟩, hzv⟩ := hx'
    have hzv' : mk L ψ z v = u x' := hzv
    exact MDifferentiableAt.comp x' (hzv' ▸ hFd z hz v) (hu x')
  have hA := RiemannSurface.analyticAt_esymm_map_fiberMultiset hp hne
    (IsManifold.chart_mem_maximalAtlas y₀) (mem_chart_source ℂ y₀) hg j
  -- The chart of `ℂ / L` at `[z₀]` read through the projection `ℂ → ℂ / L`.
  have hφ : DifferentiableAt ℂ (fun z ↦ e' (Quotient.mk (AddAction.orbitRel L ℂ) z)) z₀ :=
    mdifferentiableAt_iff_differentiableAt.1 <|
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ y₀) (mem_chart_source ℂ y₀)).comp z₀
        ((isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := 1) (G := L) (M := ℂ)).mdifferentiable
          one_ne_zero z₀)
  refine (hA.differentiableAt.comp z₀ hφ).congr_of_eventuallyEq ?_
  have hsrc : ∀ᶠ z in 𝓝 z₀, Quotient.mk (AddAction.orbitRel L ℂ) z ∈ e'.source :=
    continuous_quotient_mk'.continuousAt.preimage_mem_nhds
      (e'.open_source.mem_nhds (mem_chart_source ℂ y₀))
  filter_upwards [hsrc, hUo.mem_nhds hz₀] with z hz hzU
  simp only [Function.comp_apply]
  rw [e'.left_inv hz]
  refine congrArg (Multiset.esymm · j) (Multiset.map_congr rfl fun x hx ↦ ?_)
  have hpx : p x = Quotient.mk _ z := (RiemannSurface.mem_fiberMultiset
    (RiemannSurface.finite_preimage_singleton hp hne _)).1 hx |>.1
  rw [← mk_fiberCoord hpx, hF z hzU, fiberCoord_mk_self]

/-- **A compact curve in a flat line lies in the zero section.** Let `u` be a nonconstant
holomorphic map from a compact connected Riemann surface to the flat line of `ψ`, whose projection
to `ℂ / L` has degree `m`. Suppose that the powers `1, …, m` of the flat line have no nonzero
holomorphic section: every entire `f` with `f (z + γ) = ψ(γ)ʲ f(z)`, `1 ≤ j ≤ m`, vanishes. Then
`u` takes values in the zero section. -/
theorem range_subset_range_zeroSection (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u)
    (hne : ∃ x x', u x ≠ u x')
    (hψ : ∀ j : ℕ, 0 < j → j ≤ RiemannSurface.degree (proj L ψ ∘ u) → ∀ f : ℂ → ℂ,
      Differentiable ℂ f → (∀ (γ : L) (z : ℂ), f (z + γ) = ψ γ ^ j * f z) → f = 0) :
    range u ⊆ range (zeroSection L ψ) := by
  set p := proj L ψ ∘ u
  have hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p :=
    ((contMDiff_proj L ψ (n := 1)).mdifferentiable one_ne_zero).comp hu
  -- The projection of the curve is nonconstant, since a curve in one fibre is constant.
  obtain ⟨x₁, x₂, hp₁₂⟩ : ∃ x x', p x ≠ p x' := by
    by_contra! h
    obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
    obtain ⟨z₀, hz₀⟩ := Quotient.exists_rep (p x₀)
    obtain ⟨n, hn⟩ := exists_eq_const_of_proj_eq hu (z₀ := z₀) fun x ↦ (h x x₀).trans hz₀.symm
    obtain ⟨x, x', hxx'⟩ := hne
    exact hxx' ((hn x).trans (hn x').symm)
  have hne' := RiemannSurface.not_eventuallyConst_of_ne hp hp₁₂
  -- Each fibre has `m` points, counted with multiplicity.
  have hcard (y) : Multiset.card (RiemannSurface.fiberMultiset p y) = RiemannSurface.degree p := by
    simpa using RiemannSurface.FiniteHolomorphicMap.card_fiberMultiset
      (.ofMDifferentiable hp ⟨x₁, x₂, hp₁₂⟩) y
  -- Every `bⱼ`, `1 ≤ j ≤ m`, is a holomorphic section of the `j`-th power, hence zero, and the
  -- `bⱼ` with `j > m` vanish since `m` values enter.
  have hb (z : ℂ) (j : ℕ) (hj : 0 < j) : fiberEsymm u j z = 0 := by
    rcases le_or_gt j (RiemannSurface.degree p) with hjm | hjm
    · exact congrFun (hψ j hj hjm _ (differentiable_fiberEsymm hu hne' j) (fiberEsymm_add j)) z
    · exact Multiset.esymm_of_card_lt (by rwa [Multiset.card_map, hcard])
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := Quotient.exists_rep (p x)
  have hx : x ∈ RiemannSurface.fiberMultiset p (Quotient.mk _ z) :=
    (RiemannSurface.mem_fiberMultiset (RiemannSurface.finite_preimage_singleton hp hne' _)).2
      ⟨hz.symm, (RiemannSurface.localMultiplicity_pos_iff (.of_forall hp)).2 (hne' x)⟩
  rw [mem_range_zeroSection_iff hz.symm]
  exact Multiset.forall_esymm_eq_zero_iff.1 (hb z) _ (Multiset.mem_map_of_mem _ hx)

end Curve

end FlatLine

end TauCeti
