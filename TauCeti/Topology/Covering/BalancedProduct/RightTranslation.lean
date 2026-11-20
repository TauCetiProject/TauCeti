/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Covering.BalancedProduct.Basic

/-!
# The balanced product `G ×_K Z` of a group with a space acted on by a subgroup

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
  (`TauCeti.BalancedProduct.liftRightTranslation`), the unique `G`-equivariant map sending
  `[1, z]` to `ι z`;
* the projection `[g, z] ↦ [z]` onto the orbit space `Z ⧸ K`, the case of the projection
  `TauCeti.BalancedProduct.orbitProj` of any balanced product onto the orbit space of its second
  factor. It is `G`-invariant and its fibres are exactly the `G`-orbits, so that the orbit space
  of `G` on `G ×_K Z` is `Z ⧸ K`
  (`TauCeti.BalancedProduct.orbitRelQuotientEquivRightTranslation`).

For a topological group `G`, right translation by `K` is continuous, and it is proper when `K` is
closed: it is the restriction of Mathlib's proper action of `Gᵐᵒᵖ` on `G` along the closed
embedding `h ↦ op h⁻¹`. The smooth structure of `G ×_K Z` for a Lie group `G` is in
`TauCeti.Geometry.Lie.Subgroup.BalancedProduct`.

## Main definitions

* `Subgroup.RightTranslation K`: the group `G` as a `K`-space under `h • g = g h⁻¹`.
* `TauCeti.BalancedProduct.liftRightTranslation`: the map `[g, z] ↦ g • ι z`.

## Main results

* `TauCeti.BalancedProduct.mk_toRightTranslation_eq_mk_toRightTranslation_iff`: when two classes
  agree.
* `TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`,
  `TauCeti.BalancedProduct.orbitRelQuotientEquivRightTranslation`: the fibres of the projection
  onto `Z ⧸ K` are the `G`-orbits.
* `TauCeti.BalancedProduct.eq_liftRightTranslation`,
  `TauCeti.BalancedProduct.liftEquivRightTranslation`: `G`-equivariant maps out of `G ×_K Z`
  correspond to `K`-equivariant maps out of `Z`.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972,
  Section II.2 (twisted products `G ×_K A`).
-/

public section

/-! ### `G` as a `K`-space under right translation -/

namespace Subgroup

/-- The group `G` regarded as a space acted on by a subgroup `K` through right translation,
`h • g = g h⁻¹`. The balanced product of this `K`-space with a `K`-space `Z` is `G ×_K Z`. -/
@[expose] def RightTranslation {G : Type*} [Group G] (_K : Subgroup G) : Type _ := G

variable {G : Type*} [Group G] (K : Subgroup G)

/-- The identification of `G` with the `K`-space `Subgroup.RightTranslation K`. -/
@[expose] def toRightTranslation : G ≃ K.RightTranslation :=
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

instance : Inhabited K.RightTranslation :=
  ⟨K.toRightTranslation 1⟩

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
  QuotientGroup.mk_mul_of_mem _ (inv_mem h.property)

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
      continuous_snd).mul (continuous_subtypeVal.comp continuous_fst).inv)

/-- **Right translation by a closed subgroup is proper.** It is the restriction of Mathlib's
proper action of `Gᵐᵒᵖ` on `G` by right translation along the closed embedding `h ↦ op h⁻¹`. -/
instance [IsClosed (K : Set G)] : ProperSMul K K.RightTranslation :=
  letI : MulAction Gᵐᵒᵖ K.RightTranslation := inferInstanceAs (MulAction Gᵐᵒᵖ G)
  haveI : ProperSMul Gᵐᵒᵖ K.RightTranslation := inferInstanceAs (ProperSMul Gᵐᵒᵖ G)
  properSMul_of_isClosedEmbedding ((MulEquiv.inv' G).toMonoidHom.comp K.subtype)
    ((MulOpposite.opHomeomorph.isClosedEmbedding.comp (Homeomorph.inv G).isClosedEmbedding).comp
      ‹IsClosed (K : Set G)›.isClosedEmbedding_subtypeVal) fun _ _ ↦ rfl

end Topology

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

/-- The quotient class of `x : K.RightTranslation × Z` is the class `[g, z]` with `g` the
underlying element of `x.1` in `G`. -/
theorem quotientMk_eq_mk_toRightTranslation (x : K.RightTranslation × Z) :
    Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) x =
      mk K (K.toRightTranslation (K.toRightTranslation.symm x.1)) x.2 := by
  rw [Equiv.apply_symm_apply]

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
    (fun x ↦ (K.toRightTranslation (k * K.toRightTranslation.symm x.1), x.2)) fun _ _ ⟨h, hh⟩ ↦
      ⟨h, by simp [← hh, mul_assoc]⟩

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
      rw [smul_mk_toRightTranslation, smul_mk_toRightTranslation,
        mk_toRightTranslation_eq_mk_toRightTranslation_iff] at hy
      obtain ⟨h, hg, hz⟩ := hy
      obtain rfl : h = 1 := IsCancelSMul.right_cancel' h 1 z (by simp [hz])
      -- Now `k g = k' g`, so `k = k'`.
      simpa using hg.symm

/-! ### The projection onto `G ⧸ K` -/

/-- The projection `[g, z] ↦ g K` of `G ×_K Z` onto `G ⧸ K` is `G`-equivariant. -/
@[simp]
theorem proj_smul_rightTranslation (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    proj Z Subgroup.RightTranslation.quotientMk_smul (k • y) =
      k • proj Z Subgroup.RightTranslation.quotientMk_smul y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp [proj_mk]

/-! ### The action map to a `G`-space -/

section Lift

variable {M : Type*} [MulAction G M] (ι : Z →ₑ[((↑) : K → G)] M)

/-- The map `[g, z] ↦ g • ι z` from `G ×_K Z` to a `G`-space `M`, for a `K`-equivariant map
`ι : Z → M`. It is the unique `G`-equivariant map sending `[1, z]` to `ι z`
(`TauCeti.BalancedProduct.eq_liftRightTranslation`). -/
def liftRightTranslation : BalancedProduct K K.RightTranslation Z → M :=
  Quotient.lift (fun x ↦ K.toRightTranslation.symm x.1 • ι x.2) fun _ _ ⟨h, hh⟩ ↦ by
    simp [← hh, map_smulₛₗ, mul_smul]

@[simp]
theorem liftRightTranslation_mk (g : G) (z : Z) :
    liftRightTranslation ι (mk K (K.toRightTranslation g) z) = g • ι z :=
  (rfl)

theorem liftRightTranslation_mk_one (z : Z) :
    liftRightTranslation ι (mk K (K.toRightTranslation 1) z) = ι z := by
  simp

/-- The action map is `G`-equivariant. -/
@[simp]
theorem liftRightTranslation_smul (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    liftRightTranslation ι (k • y) = k • liftRightTranslation ι y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp [mul_smul]

/-- **The universal property of the balanced product.** A `G`-equivariant map from `G ×_K Z`
which sends `[1, z]` to `ι z` for every `z` is the action map `liftRightTranslation ι`. -/
theorem eq_liftRightTranslation {f : BalancedProduct K K.RightTranslation Z → M}
    (hf : ∀ (k : G) y, f (k • y) = k • f y) (hι : ∀ z, f (mk K (K.toRightTranslation 1) z) = ι z) :
    f = liftRightTranslation ι := by
  funext y
  induction y using induction_on_toRightTranslation with
  | h g z => rw [liftRightTranslation_mk, ← hι, ← hf, smul_mk_toRightTranslation, mul_one]

variable (K Z M) in
/-- **The universal property of the balanced product** as a bijection: `G`-equivariant maps
`G ×_K Z → M` correspond to `K`-equivariant maps `Z → M`, through
`TauCeti.BalancedProduct.liftRightTranslation` in one direction and restriction to `z ↦ [1, z]` in
the other. -/
def liftEquivRightTranslation :
    (Z →ₑ[((↑) : K → G)] M) ≃ (BalancedProduct K K.RightTranslation Z →[G] M) where
  toFun ι := ⟨liftRightTranslation ι, liftRightTranslation_smul ι⟩
  invFun f := ⟨fun z ↦ f (mk K (K.toRightTranslation 1) z), fun h z ↦ by
    rw [mk_toRightTranslation_one_smul, map_smul]⟩
  left_inv ι := by
    ext z
    exact liftRightTranslation_mk_one ι z
  right_inv f := by
    ext y
    exact congrFun (eq_liftRightTranslation _ (fun k y ↦ map_smul f k y) fun _ ↦ rfl).symm y

@[simp]
theorem liftEquivRightTranslation_apply_apply (y : BalancedProduct K K.RightTranslation Z) :
    liftEquivRightTranslation K Z M ι y = liftRightTranslation ι y :=
  (rfl)

@[simp]
theorem liftEquivRightTranslation_symm_apply_apply
    (f : BalancedProduct K K.RightTranslation Z →[G] M) (z : Z) :
    (liftEquivRightTranslation K Z M).symm f z = f (mk K (K.toRightTranslation 1) z) :=
  (rfl)

end Lift

/-! ### The projection onto `Z ⧸ K` -/

/-- The projection onto `Z ⧸ K` is constant on the orbits of `G`. -/
@[simp]
theorem orbitProj_smul (k : G) (y : BalancedProduct K K.RightTranslation Z) :
    orbitProj (k • y) = orbitProj y :=
  y.induction_on_toRightTranslation fun g z ↦ by simp

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
      obtain ⟨h, hz⟩ := Quotient.exact hq
      exact ⟨g' * (h : G)⁻¹ * g⁻¹, by simp [← hz, ← mk_toRightTranslation_mul]⟩
    · rintro ⟨k, hk⟩
      rw [smul_mk_toRightTranslation] at hk
      obtain ⟨h, -, hz⟩ := mk_toRightTranslation_eq_mk_toRightTranslation_iff.1 hk.symm
      exact Quotient.sound ⟨h⁻¹, by rw [← hz]; exact inv_smul_smul h z⟩

variable (K Z) in
/-- **The orbit space of `G` on `G ×_K Z` is `Z ⧸ K`**: the projection `[g, z] ↦ [z]` induces a
bijection from the `G`-orbits, with inverse `[z] ↦ G • [1, z]`. -/
def orbitRelQuotientEquivRightTranslation :
    MulAction.orbitRel.Quotient G (BalancedProduct K K.RightTranslation Z) ≃
      MulAction.orbitRel.Quotient K Z where
  toFun := Quotient.lift orbitProj fun _ _ hyy' ↦ (orbitProj_eq_orbitProj_iff.2 hyy').symm
  invFun := Quotient.map (mk K (K.toRightTranslation 1)) fun _ _ ⟨h, hh⟩ ↦
    ⟨h, by rw [← hh, mk_toRightTranslation_one_smul]⟩
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      induction y using induction_on_toRightTranslation with
      | h g z =>
        rw [Quotient.lift_mk, orbitProj_mk]
        exact Quotient.sound ⟨g⁻¹, by simp⟩
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h z => exact orbitProj_mk (K.toRightTranslation 1) z

@[simp]
theorem orbitRelQuotientEquivRightTranslation_mk (y : BalancedProduct K K.RightTranslation Z) :
    orbitRelQuotientEquivRightTranslation K Z (Quotient.mk _ y) = orbitProj y :=
  (rfl)

@[simp]
theorem orbitRelQuotientEquivRightTranslation_symm_mk (z : Z) :
    (orbitRelQuotientEquivRightTranslation K Z).symm (Quotient.mk _ z) =
      Quotient.mk _ (mk K (K.toRightTranslation 1) z) :=
  (rfl)

end TauCeti.BalancedProduct
