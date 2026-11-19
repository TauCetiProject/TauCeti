/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Topology.Covering.BalancedProduct.Basic
public import TauCeti.Algebra.GroupAction.Prod
public import TauCeti.Topology.Algebra.ProperAction.Basic

import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The balanced product `G ×_K Z` of a Lie group with a space acted on by a closed subgroup

Let `K` be a subgroup of a group `G` and let `K` act on a space `Z`. Regard `G` as a `K`-space
under right translation, `h • g = g h⁻¹` (`Subgroup.RightTranslation K`). The balanced product
`G ×_K Z` is then `TauCeti.BalancedProduct K (Subgroup.RightTranslation K) Z`, the quotient of
`G × Z` by the diagonal action

`h • (g, z) = (g h⁻¹, h • z)`,

that is, by the relation `(g, z) ∼ (g h, h⁻¹ • z)`. Write `[g, z]` for the class of `(g, z)`, so
that `[g h, z] = [g, h • z]` (`TauCeti.BalancedProduct.mk_toRightTranslation_mul`). The group `G`
acts on `G ×_K Z` by `k • [g, z] = [k g, z]`, freely when `K` acts freely on `Z`, and three maps
leave it:

* the projection `[g, z] ↦ g K` onto the homogeneous space `G ⧸ K`, the projection
  `TauCeti.BalancedProduct.proj` induced by the invariant map `g ↦ g K`
  (`Subgroup.RightTranslation.quotientMk_smul`); it is `G`-equivariant;
* for a `K`-equivariant map `ι : Z → M` into a `G`-space, the map `[g, z] ↦ g • ι z`
  (`TauCeti.BalancedProduct.lift`), the unique `G`-equivariant map sending `[1, z]` to `ι z`;
* the projection `[g, z] ↦ [z]` onto the orbit space `Z ⧸ K`
  (`TauCeti.BalancedProduct.orbitProj`), which is `G`-invariant and whose fibres are exactly the
  `G`-orbits, so that the orbit space of `G` on `G ×_K Z` is `Z ⧸ K`
  (`TauCeti.BalancedProduct.orbitRelQuotientEquiv`).

Now let `G` be a finite-dimensional real Lie group with boundaryless model and `K` a closed
subgroup, with a Lie group structure for which it acts smoothly on `G` by left multiplication,
such as its closed-subgroup structure (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). Let `K`
act smoothly on a Hausdorff boundaryless manifold `Z`. Right translation by `K` on `G` is free,
and it is proper because `K` is closed: if `g h⁻¹` and `g` converge then so does
`h = (g h⁻¹)⁻¹ g`. So the diagonal action of `K` on `G × Z` is free and proper
(`TauCeti.isCancelSMul_prod`, `TauCeti.properSMul_prod`), and by the quotient manifold theorem
`G ×_K Z` is a smooth manifold of dimension `dim G + dim Z - dim K`
(`TauCeti.BalancedProduct.rightTranslationChartedSpace`), for which `(g, z) ↦ [g, z]` is a smooth
submersion. The action of `G` and the three maps above are smooth, the last one when `K` acts
freely and properly on `Z`, so that `Z ⧸ K` is itself a manifold.

For a Hamiltonian action with coadjoint-equivariant moment map `μ` and a regular value `c` of
`μ`, this is the space `G ×_{G_c} μ⁻¹(c)`, with its maps to the coadjoint orbit `G ⧸ G_c`, to the
symplectic manifold and to the reduced space `μ⁻¹(c) ⧸ G_c`, through which reduction at `c` is
compared with reduction at zero of the shifted moment map on the product with the orbit.

## Main definitions

* `Subgroup.RightTranslation K`: the group `G` as a `K`-space under `h • g = g h⁻¹`.
* `TauCeti.BalancedProduct.lift`: the map `[g, z] ↦ g • ι z`.
* `TauCeti.BalancedProduct.orbitProj`: the map `[g, z] ↦ [z]` to `Z ⧸ K`.
* `TauCeti.BalancedProduct.rightTranslationChartedSpace`: the charts of the quotient manifold
  theorem on `G ×_K Z`.

## Main results

* `TauCeti.BalancedProduct.mk_toRightTranslation_eq_mk_toRightTranslation_iff`: when two classes
  agree.
* `TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`,
  `TauCeti.BalancedProduct.orbitRelQuotientEquiv`: the fibres of the projection onto `Z ⧸ K` are
  the `G`-orbits.
* `TauCeti.BalancedProduct.eq_lift`, `TauCeti.BalancedProduct.liftEquiv`: `G`-equivariant maps
  out of `G ×_K Z` correspond to `K`-equivariant maps out of `Z`.
* `TauCeti.BalancedProduct.isManifold_rightTranslation`,
  `TauCeti.BalancedProduct.isSubmersion_quotientMk_rightTranslation`: `G ×_K Z` is a smooth
  manifold and the projection from `G × Z` is a smooth submersion.
* `TauCeti.BalancedProduct.contMDiffSMul_rightTranslation`: `G` acts smoothly on `G ×_K Z`.
* `TauCeti.BalancedProduct.contMDiff_proj_rightTranslation`,
  `TauCeti.BalancedProduct.contMDiff_lift`, `TauCeti.BalancedProduct.contMDiff_orbitProj`: the
  three maps are smooth.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972,
  Section II.2 (twisted products `G ×_K A`).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
-/

public section

noncomputable section

open Function Set Filter Topology Manifold TauCeti
open scoped ContDiff Manifold

/-! ### `G` as a `K`-space under right translation -/

namespace Subgroup

/-- The group `G` regarded as a space acted on by a subgroup `K` through right translation,
`h • g = g h⁻¹`. The balanced product of this `K`-space with a `K`-space `Z` is `G ×_K Z`. -/
@[expose] def RightTranslation {G : Type*} [Group G] (_K : Subgroup G) : Type _ := G

variable {G : Type*} [Group G] (K : Subgroup G)

/-- The identification of `G` with the `K`-space `Subgroup.RightTranslation K`. -/
def toRightTranslation : G ≃ K.RightTranslation :=
  Equiv.refl _

namespace RightTranslation

variable {K}

instance : SMul K K.RightTranslation where
  smul h x := K.toRightTranslation ((K.toRightTranslation.symm x) * (h : G)⁻¹)

/-- An element `h` of `K` acts on `G` by right translation by `h⁻¹`. -/
@[simp]
theorem smul_toRightTranslation (h : K) (g : G) :
    h • K.toRightTranslation g = K.toRightTranslation (g * (h : G)⁻¹) :=
  (rfl)

@[simp]
theorem toRightTranslation_symm_smul (h : K) (x : K.RightTranslation) :
    K.toRightTranslation.symm (h • x) = K.toRightTranslation.symm x * (h : G)⁻¹ :=
  (rfl)

/-- `K` acts on `G` by `h • g = g h⁻¹`. -/
instance : MulAction K K.RightTranslation where
  one_smul x := K.toRightTranslation.symm.injective (by simp)
  mul_smul h h' x := K.toRightTranslation.symm.injective (by simp [mul_assoc])

/-- Right translation is free. -/
instance : IsCancelSMul K K.RightTranslation where
  left_cancel' h _ _ hxy := smul_left_cancel h hxy
  right_cancel' h h' x hx := by
    have h1 := congrArg K.toRightTranslation.symm hx
    simp only [toRightTranslation_symm_smul, mul_right_inj, inv_inj] at h1
    exact Subtype.ext h1

variable (K) in
/-- The coset map `g ↦ g K`, read on the `K`-space `Subgroup.RightTranslation K`. -/
def quotientMk (x : K.RightTranslation) : G ⧸ K :=
  (K.toRightTranslation.symm x : G)

@[simp]
theorem quotientMk_toRightTranslation (g : G) :
    quotientMk K (K.toRightTranslation g) = (g : G ⧸ K) :=
  (rfl)

/-- The coset map `g ↦ g K` is invariant under right translation by `K`, so it induces the
projection `TauCeti.BalancedProduct.proj` of a balanced product onto `G ⧸ K`. -/
theorem quotientMk_smul (h : K) (x : K.RightTranslation) : quotientMk K (h • x) = quotientMk K x :=
  QuotientGroup.mk_mul_of_mem _ (inv_mem h.2)

section Topology

variable [TopologicalSpace G]

instance : TopologicalSpace K.RightTranslation := inferInstanceAs (TopologicalSpace G)

instance [T2Space G] : T2Space K.RightTranslation := inferInstanceAs (T2Space G)

theorem continuous_toRightTranslation : Continuous K.toRightTranslation :=
  continuous_id

theorem continuous_toRightTranslation_symm : Continuous K.toRightTranslation.symm :=
  continuous_id

variable [IsTopologicalGroup G]

/-- Right translation is continuous. -/
instance : ContinuousSMul K K.RightTranslation where
  continuous_smul :=
    continuous_toRightTranslation.comp ((continuous_toRightTranslation_symm.comp
      continuous_snd).mul (continuous_subtype_val.comp continuous_fst).inv)

/-- **Right translation by a closed subgroup is proper.** If `g h⁻¹` and `g` converge along an
ultrafilter, then so does `h = (g h⁻¹)⁻¹ g`, to an element of the closed subgroup `K`. -/
instance [IsClosed (K : Set G)] : ProperSMul K K.RightTranslation := by
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 x₁ x₂ hx ↦ ?_⟩
  set p := K.toRightTranslation.symm
  have h₁ : Tendsto (fun q : K × K.RightTranslation ↦ p (q.1 • q.2)) 𝒰 (𝓝 (p x₁)) :=
    (continuous_toRightTranslation_symm.tendsto _).comp ((continuous_fst.tendsto _).comp hx)
  have h₂ : Tendsto (fun q : K × K.RightTranslation ↦ p q.2) 𝒰 (𝓝 (p x₂)) :=
    (continuous_toRightTranslation_symm.tendsto _).comp ((continuous_snd.tendsto _).comp hx)
  have hK : Tendsto (fun q : K × K.RightTranslation ↦ (q.1 : G)) 𝒰 (𝓝 ((p x₁)⁻¹ * p x₂)) :=
    (h₁.inv.mul h₂).congr fun q ↦ by simp [p, mul_assoc]
  have hmem : (p x₁)⁻¹ * p x₂ ∈ K :=
    IsClosed.mem_of_tendsto ‹IsClosed (K : Set G)› hK (Eventually.of_forall fun q ↦ q.1.2)
  have hK' :
      Tendsto (Prod.fst : K × K.RightTranslation → K) 𝒰 (𝓝 (⟨(p x₁)⁻¹ * p x₂, hmem⟩ : K)) := by
    rw [tendsto_subtype_rng]
    exact hK
  exact ⟨⟨(p x₁)⁻¹ * p x₂, hmem⟩, p.injective (by simp [p]), hK'⟩

end Topology

section Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]

instance : ChartedSpace H K.RightTranslation := inferInstanceAs (ChartedSpace H G)

instance {n : ℕ∞ω} [IsManifold I n G] : IsManifold I n K.RightTranslation :=
  inferInstanceAs (IsManifold I n G)

theorem contMDiff_toRightTranslation (n : ℕ∞ω) : ContMDiff I I n K.toRightTranslation :=
  contMDiff_id

theorem contMDiff_toRightTranslation_symm (n : ℕ∞ω) :
    ContMDiff I I n K.toRightTranslation.symm :=
  contMDiff_id

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F K]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]

/-- The inclusion of `K` into `G` is smooth, since it is the action of `K` on `1 ∈ G`. -/
private theorem contMDiff_subtypeVal : ContMDiff 𝓘(ℝ, F) I ∞ (fun h : K ↦ (h : G)) := by
  have h := (contMDiff_smul (I := 𝓘(ℝ, F)) (I' := I) (n := ∞) (G := K) (M := G)).comp
    (contMDiff_id.prodMk (contMDiff_const (c := (1 : G))))
  simpa [comp_def, Subgroup.smul_def] using h

/-- Right translation is smooth. -/
instance [LieGroup I ∞ G] : ContMDiffSMul 𝓘(ℝ, F) I ∞ K K.RightTranslation where
  contMDiff_smul := (contMDiff_toRightTranslation ∞).comp
    (((contMDiff_toRightTranslation_symm ∞).comp contMDiff_snd).mul
      (contMDiff_subtypeVal.comp contMDiff_fst).inv)

end Manifold

end RightTranslation

end Subgroup

namespace TauCeti.BalancedProduct

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]

/-! ### Classes `[g, z]` -/

/-- Two classes `[g, z]` and `[g', z']` of `G ×_K Z` agree exactly when `g = g' h⁻¹` and
`z = h • z'` for some `h ∈ K`. -/
theorem mk_toRightTranslation_eq_mk_toRightTranslation_iff {g g' : G} {z z' : Z} :
    mk K (K.toRightTranslation g) z = mk K (K.toRightTranslation g') z' ↔
      ∃ h : K, g' * (h : G)⁻¹ = g ∧ h • z' = z := by
  simp [mk_eq_mk_iff]

/-- **The balancing relation** `[g h, z] = [g, h • z]` of `G ×_K Z`. -/
theorem mk_toRightTranslation_mul (g : G) (h : K) (z : Z) :
    mk K (K.toRightTranslation (g * h)) z = mk K (K.toRightTranslation g) (h • z) := by
  have h₁ := mk_smul_left (E := K.RightTranslation) h (K.toRightTranslation (g * h)) (h • z)
  rw [Subgroup.RightTranslation.smul_toRightTranslation, mul_inv_cancel_right, inv_smul_smul] at h₁
  exact h₁.symm

/-- Every point of `G ×_K Z` is a class `[g, z]`. -/
@[elab_as_elim]
theorem induction_on_toRightTranslation {p : BalancedProduct K K.RightTranslation Z → Prop}
    (y : BalancedProduct K K.RightTranslation Z)
    (h : ∀ g z, p (mk K (K.toRightTranslation g) z)) : p y := by
  induction y using Quotient.inductionOn with
  | h x => simpa using h (K.toRightTranslation.symm x.1) x.2

/-! ### The action of `G` -/

instance : SMul G (BalancedProduct K K.RightTranslation Z) where
  smul k := Quotient.map
    (fun x ↦ (K.toRightTranslation (k * K.toRightTranslation.symm x.1), x.2)) fun x y hxy ↦ by
      obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
      exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨h, by simp [mul_assoc]⟩)

/-- An element `k` of `G` acts on `G ×_K Z` by `[g, z] ↦ [k g, z]`. -/
@[simp]
theorem smul_mk_toRightTranslation (k g : G) (z : Z) :
    k • mk K (K.toRightTranslation g) z = mk K (K.toRightTranslation (k * g)) z :=
  (rfl)

/-- `G` acts on `G ×_K Z` by left multiplication on the first factor. -/
instance : MulAction G (BalancedProduct K K.RightTranslation Z) where
  one_smul y := y.induction_on_toRightTranslation fun g z ↦ by simp
  mul_smul k k' y := y.induction_on_toRightTranslation fun g z ↦ by simp [mul_assoc]

/-- The inclusion `z ↦ [1, z]` of `Z` into `G ×_K Z` is `K`-equivariant. -/
theorem mk_toRightTranslation_one_smul (h : K) (z : Z) :
    mk K (K.toRightTranslation 1) (h • z) = (h : G) • mk K (K.toRightTranslation 1) z := by
  rw [smul_mk_toRightTranslation, mul_one, ← one_mul (h : G), mk_toRightTranslation_mul]

/-- **`G` acts freely on `G ×_K Z` when `K` acts freely on `Z`.** If `k • [g, z] = [g, z]`, then
`k g = g h⁻¹` and `h • z = z` for some `h ∈ K`, so `h = 1` and `k = 1`. -/
instance [IsCancelSMul K Z] : IsCancelSMul G (BalancedProduct K K.RightTranslation Z) where
  left_cancel' k _ _ hxy := smul_left_cancel k hxy
  right_cancel' k k' y hy := by
    induction y using induction_on_toRightTranslation with
    | h g z =>
      rw [← inv_smul_eq_iff, smul_smul, smul_mk_toRightTranslation,
        mk_toRightTranslation_eq_mk_toRightTranslation_iff] at hy
      obtain ⟨h, hg, hz⟩ := hy
      obtain rfl : h = 1 := IsCancelSMul.right_cancel' h 1 z (by rw [hz, one_smul])
      rw [OneMemClass.coe_one, inv_one, mul_one, ← one_mul g, ← mul_assoc, mul_one] at hg
      exact (inv_mul_eq_one.1 (mul_right_cancel hg.symm)).symm

/-! ### The projection onto `G ⧸ K` -/

/-- The projection `[g, z] ↦ g K` of `G ×_K Z` onto `G ⧸ K` is `G`-equivariant. -/
@[simp]
theorem proj_quotientMk_smul (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    proj Z Subgroup.RightTranslation.quotientMk_smul (k • y) =
      k • proj Z Subgroup.RightTranslation.quotientMk_smul y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp [proj_mk]

/-! ### The action map to a `G`-space -/

section Lift

variable {M : Type*} [MulAction G M] (ι : Z →ₑ[((↑) : K → G)] M)

/-- The map `[g, z] ↦ g • ι z` from `G ×_K Z` to a `G`-space `M`, for a `K`-equivariant map
`ι : Z → M`. It is the unique `G`-equivariant map sending `[1, z]` to `ι z`
(`TauCeti.BalancedProduct.eq_lift`). -/
def lift : BalancedProduct K K.RightTranslation Z → M :=
  Quotient.lift (fun x ↦ K.toRightTranslation.symm x.1 • ι x.2) fun x y hxy ↦ by
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    simp only [Prod.smul_fst, Prod.smul_snd, Subgroup.RightTranslation.toRightTranslation_symm_smul]
    rw [map_smulₛₗ ι h, mul_smul, inv_smul_smul]

@[simp]
theorem lift_mk (g : G) (z : Z) : lift ι (mk K (K.toRightTranslation g) z) = g • ι z :=
  (rfl)

theorem lift_mk_one (z : Z) : lift ι (mk K (K.toRightTranslation 1) z) = ι z := by
  simp

/-- The action map is `G`-equivariant. -/
@[simp]
theorem lift_smul (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    lift ι (k • y) = k • lift ι y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp [mul_smul]

/-- **The universal property of the balanced product.** A `G`-equivariant map from `G ×_K Z`
which sends `[1, z]` to `ι z` for every `z` is the action map `lift ι`. -/
theorem eq_lift {f : BalancedProduct K K.RightTranslation Z → M}
    (hf : ∀ (k : G) y, f (k • y) = k • f y) (hι : ∀ z, f (mk K (K.toRightTranslation 1) z) = ι z) :
    f = lift ι := by
  funext y
  induction y using induction_on_toRightTranslation with
  | h g z => rw [lift_mk, ← hι, ← hf, smul_mk_toRightTranslation, mul_one]

variable (K Z M) in
/-- **The universal property of the balanced product** as a bijection: `G`-equivariant maps
`G ×_K Z → M` correspond to `K`-equivariant maps `Z → M`, through `TauCeti.BalancedProduct.lift`
in one direction and restriction to `z ↦ [1, z]` in the other. -/
def liftEquiv :
    (Z →ₑ[((↑) : K → G)] M) ≃ (BalancedProduct K K.RightTranslation Z →[G] M) where
  toFun ι := ⟨lift ι, lift_smul ι⟩
  invFun f := ⟨fun z ↦ f (mk K (K.toRightTranslation 1) z), fun h z ↦ by
    rw [mk_toRightTranslation_one_smul, map_smul]⟩
  left_inv ι := by
    ext z
    exact lift_mk_one ι z
  right_inv f := by
    ext y
    exact congrFun (eq_lift _ (fun k y ↦ map_smul f k y) fun _ ↦ rfl).symm y

@[simp]
theorem liftEquiv_apply_apply (y : BalancedProduct K K.RightTranslation Z) :
    liftEquiv K Z M ι y = lift ι y :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply_apply (f : BalancedProduct K K.RightTranslation Z →[G] M) (z : Z) :
    (liftEquiv K Z M).symm f z = f (mk K (K.toRightTranslation 1) z) :=
  (rfl)

end Lift

/-! ### The projection onto `Z ⧸ K` -/

/-- The projection `[g, z] ↦ [z]` of `G ×_K Z` onto the orbit space `Z ⧸ K`. -/
def orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z :=
  Quotient.map Prod.snd fun x y hxy ↦ by
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨h, rfl⟩)

@[simp]
theorem orbitProj_mk (g : G) (z : Z) :
    orbitProj (mk K (K.toRightTranslation g) z) = Quotient.mk (MulAction.orbitRel K Z) z :=
  (rfl)

/-- The projection onto `Z ⧸ K` is constant on the orbits of `G`. -/
@[simp]
theorem orbitProj_smul (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    orbitProj (k • y) = orbitProj y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp

theorem orbitProj_surjective :
    Surjective (orbitProj : BalancedProduct K K.RightTranslation Z → _) := by
  intro q
  induction q using Quotient.inductionOn with
  | h z => exact ⟨mk K (K.toRightTranslation 1) z, rfl⟩

/-- **The fibres of the projection onto `Z ⧸ K` are the orbits of `G`.** Two points of `G ×_K Z`
have the same image in `Z ⧸ K` exactly when they lie in the same `G`-orbit. -/
theorem orbitProj_eq_orbitProj_iff {y y' : BalancedProduct K K.RightTranslation Z} :
    orbitProj y = orbitProj y' ↔ ∃ k : G, k • y = y' := by
  induction y using induction_on_toRightTranslation with
  | h g z =>
  induction y' using induction_on_toRightTranslation with
  | h g' z' =>
    rw [orbitProj_mk, orbitProj_mk]
    constructor
    · intro hq
      obtain ⟨h, hz⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hq))
      refine ⟨g' * (h : G)⁻¹ * g⁻¹, ?_⟩
      rw [smul_mk_toRightTranslation, inv_mul_cancel_right, ← hz, ← mk_toRightTranslation_mul,
        inv_mul_cancel_right]
    · rintro ⟨k, hk⟩
      rw [smul_mk_toRightTranslation] at hk
      obtain ⟨h, -, hz⟩ := mk_toRightTranslation_eq_mk_toRightTranslation_iff.1 hk.symm
      exact Quotient.sound (MulAction.orbitRel_apply.2
        (MulAction.mem_orbit_iff.2 ⟨h⁻¹, by rw [← hz, inv_smul_smul]⟩))

variable (K Z) in
/-- **The orbit space of `G` on `G ×_K Z` is `Z ⧸ K`**: the projection `[g, z] ↦ [z]` induces a
bijection from the `G`-orbits, with inverse `[z] ↦ G • [1, z]`. -/
def orbitRelQuotientEquiv :
    MulAction.orbitRel.Quotient G (BalancedProduct K K.RightTranslation Z) ≃
      MulAction.orbitRel.Quotient K Z where
  toFun := Quotient.lift orbitProj fun y y' hyy' ↦
    (orbitProj_eq_orbitProj_iff.2
      (MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hyy'))).symm
  invFun := Quotient.map (mk K (K.toRightTranslation 1)) fun z z' hzz' ↦ by
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hzz')
    exact MulAction.orbitRel_apply.2
      (MulAction.mem_orbit_iff.2 ⟨h, (mk_toRightTranslation_one_smul h z').symm⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      induction y using induction_on_toRightTranslation with
      | h g z =>
        refine Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, ?_⟩))
        simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h z => rfl

@[simp]
theorem orbitRelQuotientEquiv_mk (y : BalancedProduct K K.RightTranslation Z) :
    orbitRelQuotientEquiv K Z (Quotient.mk _ y) = orbitProj y :=
  (rfl)

/-! ### The manifold structure -/

section Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ EZ] [IZ.Boundaryless]
  [IsManifold IZ ∞ Z] [FiniteDimensional ℝ F] [LieGroup 𝓘(ℝ, F) ∞ K]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G] in
include I IZ F in
/-- The hypotheses of the quotient manifold theorem for the diagonal action of `K` on `G × Z`,
other than those found by instance search. -/
private theorem quotient_hypotheses :
    ProperSMul K (K.RightTranslation × Z) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  infer_instance

variable (K Z I IZ F) in
/-- **The charts of the balanced product** `G ×_K Z`: the slice charts of the quotient manifold
theorem `ProperSMul.orbitRelQuotientChartedSpace` for the free and proper diagonal action of `K`
on `G × Z`, modelled on `ℝ^(dim G + dim Z - dim K)`. -/
@[instance_reducible]
def rightTranslationChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace F (E × EZ))
      (BalancedProduct K K.RightTranslation Z) :=
  haveI := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K (I.prod IZ) (K.RightTranslation × Z)

/-- **The balanced product is a smooth manifold**, for the charts
`TauCeti.BalancedProduct.rightTranslationChartedSpace`. -/
theorem isManifold_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (BalancedProduct K K.RightTranslation Z) := by
  have := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- The projection `G × Z → G ×_K Z` is a smooth submersion. -/
theorem isSubmersion_quotientMk_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsSubmersion (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  have := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  exact ProperSMul.isSubmersion_quotientMk

/-- Smoothness descends from `G × Z` to `G ×_K Z`: a map out of the balanced product is `C^m`,
for `m ≤ ∞`, exactly when its composite with the projection is. -/
theorem contMDiff_iff_rightTranslation {EP HP : Type*} [NormedAddCommGroup EP]
    [NormedSpace ℝ EP] [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} {P : Type*}
    [TopologicalSpace P] [ChartedSpace HP P] {m : ℕ∞ω} (hm : m ≤ ∞)
    {f : BalancedProduct K K.RightTranslation Z → P} :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IP m f ↔
      ContMDiff (I.prod IZ) IP m
        (f ∘ Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  exact ((isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ)
    (F := F)).contMDiff_comp_iff Quotient.mk_surjective hm).symm

/-- **`G` acts smoothly on the balanced product.** The action lifts along the submersion
`(k, (g, z)) ↦ (k, [g, z])` to `(k, (g, z)) ↦ (k g, z)`, followed by the projection. -/
theorem contMDiffSMul_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ G
      (BalancedProduct K K.RightTranslation Z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := isManifold_rightTranslation (I := I) (IZ := IZ) (K := K) (Z := Z) (F := F)
  have hπ := isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ) (K := K) (Z := Z)
    (F := F)
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap Quotient.mk_surjective) le_rfl).1 ?_⟩
  -- On representatives the action is left multiplication on the first factor.
  have hcomp : (fun p : G × BalancedProduct K K.RightTranslation Z ↦ p.1 • p.2) ∘
      Prod.map id (Quotient.mk _) = Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) ∘
        fun p : G × (K.RightTranslation × Z) ↦
          (K.toRightTranslation (p.1 * K.toRightTranslation.symm p.2.1), p.2.2) :=
    (rfl)
  rw [hcomp]
  exact hπ.contMDiff.comp
    (((Subgroup.RightTranslation.contMDiff_toRightTranslation (I := I) ∞).comp (contMDiff_fst.mul
      ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
        contMDiff_snd.fst))).prodMk contMDiff_snd.snd)

/-- **The projection onto `G ⧸ K` is smooth**, for the charts of the homogeneous space
`Subgroup.quotientChartedSpaceOfIsClosed`. -/
theorem contMDiff_proj_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, Subgroup.QuotientModelSpace I K) ∞
      (proj Z (Subgroup.RightTranslation.quotientMk_smul (K := K))) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  have hcomp : proj Z (Subgroup.RightTranslation.quotientMk_smul (K := K)) ∘
      Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) =
        Subgroup.RightTranslation.quotientMk K ∘ Prod.fst :=
    funext fun x ↦ proj_mk Z Subgroup.RightTranslation.quotientMk_smul x.1 x.2
  rw [hcomp]
  exact (Subgroup.contMDiff_quotientMk ‹_›).comp
    ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
      (contMDiff_fst (J := IZ) (N := Z)))

/-- **The action map to a `G`-manifold is smooth** when the `K`-equivariant map `ι` is. -/
theorem contMDiff_lift {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
    [ChartedSpace HM M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
    {ι : Z →ₑ[((↑) : K → G)] M} (hι : ContMDiff IZ IM ∞ ι) :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞ (lift ι) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := IZ) (N := Z))).smul (hι.comp contMDiff_snd)

/-- **The projection onto `Z ⧸ K` is smooth** when `K` acts freely and properly on `Z`, for the
charts `ProperSMul.orbitRelQuotientChartedSpace` of the quotient manifold theorem on `Z ⧸ K`. -/
theorem contMDiff_orbitProj [ProperSMul K Z] [IsCancelSMul K Z] :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F EZ) ∞
      (orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  exact ProperSMul.contMDiff_quotientMk.comp (contMDiff_snd (I := I) (M := K.RightTranslation))

end Manifold

end TauCeti.BalancedProduct
