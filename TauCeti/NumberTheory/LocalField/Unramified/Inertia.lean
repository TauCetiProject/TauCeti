/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Quotient
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal

import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The inertia subgroup of the absolute Galois group of a local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, let `K^{alg}` be
its algebraic closure, and let `G_K = Field.absoluteGaloisGroup K = Gal(K^{alg}/K)`. This file
defines the **inertia subgroup**

`TauCeti.inertiaSubgroup K ≤ G_K`,

the automorphisms of `K^{alg}` fixing the maximal unramified extension `K^{ur}` of `K` inside
`K^{alg}`, so that `IntermediateField.fixingSubgroupEquiv` identifies it with `Gal(K^{alg}/K^{ur})`.
It is a closed normal subgroup, and it sits in the exact sequence

`1 → I_K → G_K → Gal(K^{ur}/K) → 1`

given by restriction `TauCeti.restrictMaximalUnramifiedHom K`, which is surjective with kernel
`I_K`; the unramified quotient `G_K ⧸ I_K` is identified with `Gal(K^{ur}/K)` as a topological
group. A finite separable subextension of `K^{alg}/K` is unramified exactly when inertia fixes it.

An **arithmetic Frobenius lift** is an element of `G_K` restricting to the arithmetic Frobenius
`TauCeti.maximalUnramifiedFrobenius` of `K^{ur}/K`; equivalently, it raises every root of every
polynomial `X^{q^f} − X`, `f ≠ 0`, to the `q`-th power. Lifts exist, they form a single left coset
of `I_K`, and each of them generates `G_K` topologically together with `I_K`.

## Main definitions

* `TauCeti.inertiaSubgroup K`: the inertia subgroup `I_K` of `G_K`.
* `TauCeti.restrictMaximalUnramifiedHom K`: restriction `G_K →* Gal(K^{ur}/K)`.
* `TauCeti.unramifiedQuotient K`, `TauCeti.unramifiedDegree K`: the quotient `G_K ⧸ I_K` and its
  canonical quotient map.
* `TauCeti.quotientInertiaSubgroupEquiv K`: the unramified quotient `G_K ⧸ I_K ≃ₜ* Gal(K^{ur}/K)`.
* `TauCeti.IsArithFrobeniusLift K σ`: `σ ∈ G_K` restricts to the arithmetic Frobenius of `K^{ur}`.

## Main results

* `TauCeti.mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self`: `σ ∈ I_K` exactly when `σ` fixes the
  roots of the polynomials `X^{q^f} − X`.
* `TauCeti.isClosed_inertiaSubgroup`, `TauCeti.inertiaSubgroup_normal`: `I_K` is closed and normal.
* `TauCeti.restrictMaximalUnramifiedHom_surjective`, `TauCeti.ker_restrictMaximalUnramifiedHom`:
  restriction `G_K → Gal(K^{ur}/K)` is surjective with kernel `I_K`.
* `TauCeti.unramifiedDegree_surjective`, `TauCeti.continuous_unramifiedDegree`,
  `TauCeti.ker_unramifiedDegree`: the quotient map `G_K → G_K ⧸ I_K` is a continuous surjection
  with kernel `I_K`.
* `TauCeti.inertiaSubgroup_le_fixingSubgroup_iff`: a finite separable subextension is unramified
  exactly when `I_K` fixes it.
* `TauCeti.isArithFrobeniusLift_iff`, `TauCeti.exists_isArithFrobeniusLift`,
  `TauCeti.IsArithFrobeniusLift.setOf_eq_leftCoset`: the arithmetic Frobenius lifts are
  characterised by their action on the roots of the polynomials `X^{q^f} − X`, exist, and form a
  left coset of `I_K`.
* `TauCeti.IsArithFrobeniusLift.topologicalClosure_zpowers_sup_inertiaSubgroup`: a Frobenius lift
  and `I_K` generate `G_K` topologically.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open ValuativeRel IntermediateField Pointwise

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-! ### The inertia subgroup -/

/-- **The inertia subgroup** `I_K` of the absolute Galois group of a nonarchimedean local field `K`:
the automorphisms of the algebraic closure fixing the maximal unramified extension `K^{ur}`. Through
`IntermediateField.fixingSubgroupEquiv` it is `Gal(K^{alg}/K^{ur})`. -/
def inertiaSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  (maximalUnramifiedExtension K (AlgebraicClosure K)).fixingSubgroup

/-- The inertia subgroup is the fixing subgroup of the maximal unramified extension. -/
theorem inertiaSubgroup_def :
    inertiaSubgroup K = (maximalUnramifiedExtension K (AlgebraicClosure K)).fixingSubgroup :=
  -- `(rfl)`, not `rfl`: keep the body opaque while exporting this equation across modules.
  (rfl)

variable {K} in
/-- An automorphism lies in the inertia subgroup exactly when it fixes every element of the
maximal unramified extension. -/
@[simp]
theorem mem_inertiaSubgroup_iff {σ : Field.absoluteGaloisGroup K} :
    σ ∈ inertiaSubgroup K ↔
      ∀ x ∈ maximalUnramifiedExtension K (AlgebraicClosure K),
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x = x :=
  mem_fixingSubgroup_iff _ _

variable {K} in
/-- **Inertia, through the roots of `X^{q^f} − X`.** An automorphism of `K^{alg}` lies in the
inertia subgroup exactly when it fixes every root of every polynomial `X^{q^f} − X` with `f ≠ 0`,
where `q` is the cardinality of the residue field of `K`. -/
theorem mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self {σ : Field.absoluteGaloisGroup K} :
    σ ∈ inertiaSubgroup K ↔
      ∀ (x : AlgebraicClosure K) (f : ℕ), f ≠ 0 → x ^ Nat.card 𝓀[K] ^ f = x →
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x = x := by
  rw [mem_inertiaSubgroup_iff, maximalUnramifiedExtension_eq_adjoin]
  refine ⟨fun h x f hf hx ↦ h x (subset_adjoin _ _ ⟨f, hf, hx⟩), fun h x hx ↦ ?_⟩
  -- The field fixed by `σ` contains the generators of `K^{ur}`, hence `K^{ur}` itself.
  have hle : adjoin K {y : AlgebraicClosure K | ∃ f ≠ 0, y ^ Nat.card 𝓀[K] ^ f = y} ≤
      fixedField (Subgroup.zpowers (σ : Gal(AlgebraicClosure K/K))) :=
    adjoin_le_iff.2 fun y ⟨f, hf, hy⟩ ↦ (mem_fixedField_zpowers_iff _ y).2 (h y f hf hy)
  exact (mem_fixedField_zpowers_iff _ x).1 (hle hx)

/-- **The inertia subgroup is closed** in the Krull topology. -/
theorem isClosed_inertiaSubgroup :
    IsClosed (inertiaSubgroup K : Set (Field.absoluteGaloisGroup K)) :=
  fixingSubgroup_isClosed_of_isAlgebraic _

/-- **The inertia subgroup is normal**, since `K^{ur}/K` is normal. -/
instance inertiaSubgroup_normal : (inertiaSubgroup K).Normal :=
  (maximalUnramifiedExtension K (AlgebraicClosure K)).fixingSubgroup_normal

/-! ### The exact sequence `1 → I_K → G_K → Gal(K^{ur}/K) → 1` -/

/-- Restriction of automorphisms of `K^{alg}` to the maximal unramified extension, as a homomorphism
`G_K →* Gal(K^{ur}/K)`. It is `AlgEquiv.restrictNormalHom`, typed at `Field.absoluteGaloisGroup K`,
whose group structure is not reducibly that of `Gal(K^{alg}/K)`. -/
def restrictMaximalUnramifiedHom :
    Field.absoluteGaloisGroup K →* Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) :=
  AlgEquiv.restrictNormalHom _

variable {K} in
/-- Restricting `σ` to `K^{ur}` agrees with `σ` on underlying elements: its value at `x ∈ K^{ur}`
is `σ x`. -/
@[simp]
theorem restrictMaximalUnramifiedHom_coe_apply (σ : Field.absoluteGaloisGroup K)
    (x : maximalUnramifiedExtension K (AlgebraicClosure K)) :
    (restrictMaximalUnramifiedHom K σ x : AlgebraicClosure K) =
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ (x : AlgebraicClosure K) :=
  AlgEquiv.restrictNormal_commutes _ _ x

/-- Restriction to `K^{ur}` is continuous. -/
theorem continuous_restrictMaximalUnramifiedHom : Continuous (restrictMaximalUnramifiedHom K) :=
  InfiniteGalois.restrictNormalHom_continuous _

/-- **Restriction to `K^{ur}` is surjective**: every automorphism of `K^{ur}/K` extends to
`K^{alg}`. -/
theorem restrictMaximalUnramifiedHom_surjective :
    Function.Surjective (restrictMaximalUnramifiedHom K) :=
  AlgEquiv.restrictNormalHom_surjective _

/-- **The inertia subgroup is the kernel of restriction to `K^{ur}`**. With
`TauCeti.restrictMaximalUnramifiedHom_surjective`, this is the exactness of
`1 → I_K → G_K → Gal(K^{ur}/K) → 1`. -/
theorem ker_restrictMaximalUnramifiedHom :
    (restrictMaximalUnramifiedHom K).ker = inertiaSubgroup K :=
  restrictNormalHom_ker _

/-- **The unramified quotient** `G_K ⧸ I_K` of the absolute Galois group. -/
abbrev unramifiedQuotient := Field.absoluteGaloisGroup K ⧸ inertiaSubgroup K

/-- The canonical quotient map from the absolute Galois group to its unramified quotient. -/
def unramifiedDegree : Field.absoluteGaloisGroup K →* unramifiedQuotient K :=
  QuotientGroup.mk' (inertiaSubgroup K)

/-- The unramified degree map `G_K → G_K ⧸ I_K` is surjective. -/
theorem unramifiedDegree_surjective : Function.Surjective (unramifiedDegree K) :=
  QuotientGroup.mk'_surjective _

/-- The unramified degree map `G_K → G_K ⧸ I_K` is continuous. -/
theorem continuous_unramifiedDegree : Continuous (unramifiedDegree K) :=
  continuous_quot_mk

/-- The kernel of the unramified degree map is the inertia subgroup. -/
theorem ker_unramifiedDegree : (unramifiedDegree K).ker = inertiaSubgroup K :=
  QuotientGroup.ker_mk' _

variable {K} in
/-- The unramified degree of `σ` is trivial exactly when `σ` lies in the inertia subgroup. -/
@[simp]
theorem unramifiedDegree_eq_one_iff {σ : Field.absoluteGaloisGroup K} :
    unramifiedDegree K σ = 1 ↔ σ ∈ inertiaSubgroup K :=
  QuotientGroup.eq_one_iff σ

/-- **The unramified quotient** of the absolute Galois group: restriction to the maximal unramified
extension induces an isomorphism of topological groups `G_K ⧸ I_K ≃ₜ* Gal(K^{ur}/K)`. -/
def quotientInertiaSubgroupEquiv :
    unramifiedQuotient K ≃ₜ*
      Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) :=
  -- `inertiaSubgroup K` is by definition the fixing subgroup of `K^{ur}`.
  absoluteGaloisGroupQuotientEquiv K (maximalUnramifiedExtension K (AlgebraicClosure K))

variable {K} in
/-- Identifying the unramified quotient with `Gal(K^{ur}/K)` carries the unramified degree of `σ`
to its restriction to `K^{ur}`. -/
@[simp]
theorem quotientInertiaSubgroupEquiv_unramifiedDegree (σ : Field.absoluteGaloisGroup K) :
    quotientInertiaSubgroupEquiv K (unramifiedDegree K σ) =
      restrictMaximalUnramifiedHom K σ :=
  -- `restrictMaximalUnramifiedHom K` is by definition `AlgEquiv.restrictNormalHom`.
  absoluteGaloisGroupQuotientEquiv_mk σ

variable {K} in
/-- The inverse identification of `Gal(K^{ur}/K)` with the unramified quotient sends the
restriction of `σ` to `K^{ur}` back to the unramified degree of `σ`; with
`TauCeti.restrictMaximalUnramifiedHom_surjective` this computes it on every element. -/
@[simp]
theorem quotientInertiaSubgroupEquiv_symm_restrictMaximalUnramifiedHom
    (σ : Field.absoluteGaloisGroup K) :
    (quotientInertiaSubgroupEquiv K).symm (restrictMaximalUnramifiedHom K σ) =
      unramifiedDegree K σ :=
  -- `restrictMaximalUnramifiedHom K` is by definition `AlgEquiv.restrictNormalHom`.
  absoluteGaloisGroupQuotientEquiv_symm_restrictNormalHom σ

variable {K} in
/-- **Unramified subextensions are those fixed by inertia.** A finite separable subextension `E` of
`K^{alg}/K`, with a structure of nonarchimedean local field compatible with `K`, is unramified over
`K` exactly when every element of the inertia subgroup fixes it.

Separability cannot be dropped: in positive characteristic a purely inseparable extension of `K`
is fixed by all of `G_K`, but it is ramified. -/
theorem inertiaSubgroup_le_fixingSubgroup_iff (E : IntermediateField K (AlgebraicClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
    [Algebra.IsSeparable K E] :
    inertiaSubgroup K ≤ E.fixingSubgroup ↔ IsUnramified K E := by
  rw [← E.le_maximalUnramifiedExtension_iff]
  refine ⟨fun h ↦ ?_, fixingSubgroup_le⟩
  -- `K^{ur}` is separable, so it is the separable part of the field fixed by its fixing subgroup.
  set M := maximalUnramifiedExtension K (AlgebraicClosure K)
  have hM : M ≤ separableClosure K (AlgebraicClosure K) := le_separableClosure K _ M
  have hfix := fixedField_fixingSubgroup_lift_inf_separableClosure (restrict hM)
  rw [lift_restrict] at hfix
  rw [← hfix]
  exact le_inf (((le_iff_le _ E).2 le_rfl).trans (fixedField_antitone h))
    (le_separableClosure K _ E)

/-! ### Arithmetic Frobenius lifts -/

/-- An **arithmetic Frobenius lift** is an element of the absolute Galois group of `K` whose
restriction to the maximal unramified extension is its arithmetic Frobenius
`TauCeti.maximalUnramifiedFrobenius`. By `TauCeti.isArithFrobeniusLift_iff` these are the
automorphisms of `K^{alg}` raising every root of every `X^{q^f} − X`, `f ≠ 0`, to the `q`-th
power. -/
def IsArithFrobeniusLift (σ : Field.absoluteGaloisGroup K) : Prop :=
  restrictMaximalUnramifiedHom K σ = maximalUnramifiedFrobenius K (AlgebraicClosure K)

variable {K}

/-- `σ` is an arithmetic Frobenius lift exactly when it restricts to the arithmetic Frobenius of
`K^{ur}`. -/
@[simp]
theorem isArithFrobeniusLift_def {σ : Field.absoluteGaloisGroup K} :
    IsArithFrobeniusLift K σ ↔
      restrictMaximalUnramifiedHom K σ = maximalUnramifiedFrobenius K (AlgebraicClosure K) :=
  Iff.rfl

/-- **Frobenius lifts, through the roots of `X^{q^f} − X`.** An automorphism of `K^{alg}` is an
arithmetic Frobenius lift exactly when it raises every root of every polynomial `X^{q^f} − X` with
`f ≠ 0` to the `q`-th power, where `q` is the cardinality of the residue field of `K`. -/
theorem isArithFrobeniusLift_iff {σ : Field.absoluteGaloisGroup K} :
    IsArithFrobeniusLift K σ ↔
      ∀ (x : AlgebraicClosure K) (f : ℕ), f ≠ 0 → x ^ Nat.card 𝓀[K] ^ f = x →
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x = x ^ Nat.card 𝓀[K] := by
  set M := maximalUnramifiedExtension K (AlgebraicClosure K)
  rw [isArithFrobeniusLift_def, eq_maximalUnramifiedFrobenius_iff]
  refine ⟨fun h x f hf hx ↦ ?_, fun h y f hf hy ↦ Subtype.ext ?_⟩
  · -- A root of `X^{q^f} − X` lies in `K^{ur}`, where `σ` acts through its restriction.
    have hxM : x ∈ M := (maximalUnramifiedExtension_eq_adjoin K _).ge
      (subset_adjoin _ _ ⟨f, hf, hx⟩)
    have h' := congrArg Subtype.val (h ⟨x, hxM⟩ f hf (Subtype.ext (by simpa using hx)))
    rwa [restrictMaximalUnramifiedHom_coe_apply, SubmonoidClass.coe_pow] at h'
  · rw [restrictMaximalUnramifiedHom_coe_apply, SubmonoidClass.coe_pow]
    exact h y f hf (by rw [← SubmonoidClass.coe_pow, hy])

variable (K) in
/-- **Arithmetic Frobenius lifts exist**, since restriction to `K^{ur}` is surjective. -/
theorem exists_isArithFrobeniusLift : ∃ σ : Field.absoluteGaloisGroup K, IsArithFrobeniusLift K σ :=
  restrictMaximalUnramifiedHom_surjective K _

namespace IsArithFrobeniusLift

variable {σ : Field.absoluteGaloisGroup K}

/-- Given one arithmetic Frobenius lift `σ`, an element `τ` is another exactly when `σ⁻¹ τ` lies in
the inertia subgroup. -/
theorem isArithFrobeniusLift_iff_inv_mul_mem (hσ : IsArithFrobeniusLift K σ)
    {τ : Field.absoluteGaloisGroup K} :
    IsArithFrobeniusLift K τ ↔ σ⁻¹ * τ ∈ inertiaSubgroup K := by
  rw [← ker_restrictMaximalUnramifiedHom, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    isArithFrobeniusLift_def.1 hσ, isArithFrobeniusLift_def, eq_comm]

/-- **The arithmetic Frobenius lifts form a left coset of the inertia subgroup**: they are the
elements of `σ I_K`, for any one of them `σ`. -/
theorem setOf_eq_leftCoset (hσ : IsArithFrobeniusLift K σ) :
    {τ | IsArithFrobeniusLift K τ} = σ • (inertiaSubgroup K : Set (Field.absoluteGaloisGroup K)) :=
  Set.ext fun _ ↦ (hσ.isArithFrobeniusLift_iff_inv_mul_mem).trans (mem_leftCoset_iff σ).symm

/-- **A Frobenius lift and inertia generate the absolute Galois group topologically**: the closure
of the subgroup generated by an arithmetic Frobenius lift and the inertia subgroup is `G_K`. -/
theorem topologicalClosure_zpowers_sup_inertiaSubgroup (hσ : IsArithFrobeniusLift K σ) :
    (Subgroup.zpowers σ ⊔ inertiaSubgroup K).topologicalClosure = ⊤ := by
  set r := restrictMaximalUnramifiedHom K
  set C := (Subgroup.zpowers σ ⊔ inertiaSubgroup K).topologicalClosure
  have : T2Space Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) := krullTopology_t2
  have hker : r.ker ≤ C := by
    rw [ker_restrictMaximalUnramifiedHom]
    exact le_sup_right.trans (Subgroup.le_topologicalClosure _)
  -- Restriction carries the compact closure onto the closure of the image, which contains
  -- Frobenius and is therefore the whole Galois group.
  have hmap : C.map r = ⊤ := by
    rw [r.map_topologicalClosure (continuous_restrictMaximalUnramifiedHom K) _
      (Subgroup.isClosed_topologicalClosure _).isCompact]
    refine top_le_iff.1 ?_
    rw [← topologicalClosure_zpowers_maximalUnramifiedFrobenius]
    exact Subgroup.topologicalClosure_mono (by
      rw [Subgroup.zpowers_le, ← isArithFrobeniusLift_def.1 hσ]
      exact Subgroup.mem_map_of_mem r
        (le_sup_left (b := inertiaSubgroup K) (Subgroup.mem_zpowers σ)))
  rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]

end IsArithFrobeniusLift

end TauCeti
