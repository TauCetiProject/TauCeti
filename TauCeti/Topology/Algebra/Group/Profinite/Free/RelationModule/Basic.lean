/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.Topology
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet

/-!
# Lyndon's theorem for the relation module of a profinite presentation

Let `G` be a finite group, `g : ι → G` a generating family indexed by a finite type, `F` the free
profinite group on `ι`, and `R` the kernel of the continuous homomorphism `π = lift g : F → G`
sending the generators to the `g i`. This file identifies the abelian pro-`p` group
`R^ab(p) = abelianizationProP p F R`, with the conjugation action of `F ⧸ R`, with the relation
module `relationModule ℤ_[p] G g` of the family `g`, the kernel of `ℤ_p[G]^ι → ℤ_p[G]`,
`e_i ↦ g i - 1`. Through this identification a `ℤ_p[G]`-module map out of the relation module acts
on the kernel `R^ab(p)` of the group extension `F ⧸ K → G`, for `K` the kernel of `R → R^ab(p)`;
this is how the relation module enters the computation of the number of generators of the
absolute Galois group of a `p`-adic field (NSW (7.4.1)).

The comparison map is the **Fox derivative read in `ℤ_p[G]`**: the unique continuous map
`D : F → ℤ_p[G]^ι` with `D (f * f') = D f + π f • D f'` and `D (of i) = e_i`
(`TauCeti.freeProfiniteGroup.foxDerivative`). It exists because a continuous homomorphism from
`F` to the semidirect product of `G` by `ℤ_p^{G × ι}` may take any values on the generators. Its
values satisfy the fundamental formula of Fox calculus `∑ i, D f i * (g i - 1) = π f - 1`, so on
`R` it is an equivariant homomorphism into the relation module, and it factors through `R^ab(p)`.

The inverse is written down on the Schreier generators: for a set-theoretic section `s` of `π`
the elements `r h i = s h * of i * s (h * g i)⁻¹` lie in `R`, and `m ↦ ∑ (m i)(h) • [r h i]` is
inverse to the Fox derivative on the relation module. That it is a left inverse is the uniqueness
of crossed homomorphisms on `F` with given values on the generators, applied to the crossed
homomorphism `f ↦ (x ↦ [s x⁻¹ * f * s (x⁻¹ * π f)⁻¹])` with values in the coinduced module
`G → R^ab(p)`; that it is a right inverse is a computation with the relation
`∑ m i * (g i - 1) = 0`.

## Main definitions

* `TauCeti.freeProfiniteGroup.foxDerivative`: the Fox derivative `F → ℤ_p[G]^ι` along `lift g`.
* `TauCeti.freeProfiniteGroup.abelianizationProPEquivRelationModule`: Lyndon's isomorphism
  `R^ab(p) ≃+ relationModule ℤ_[p] G g`.

## Main results

* `TauCeti.freeProfiniteGroup.foxDerivative_unique`: the Fox derivative is the unique continuous
  crossed homomorphism with values `e_i` on the generators.
* `TauCeti.freeProfiniteGroup.sum_foxDerivative_mul_sub_one`: the fundamental formula of Fox
  calculus, `∑ i, D f i * (g i - 1) = π f - 1`.
* `TauCeti.freeProfiniteGroup.foxDerivative_mem_relationModule`: the Fox derivative maps `R` into
  the relation module.
* `TauCeti.freeProfiniteGroup.coe_abelianizationProPEquivRelationModule_ofMul`: Lyndon's
  isomorphism sends the class of `r ∈ R` to the Fox derivative of `r`.
* `TauCeti.freeProfiniteGroup.abelianizationProPEquivRelationModule_padicPow`: Lyndon's
  isomorphism is compatible with `p`-adic powers on `R^ab(p)` and `ℤ_p`-scalars on the relation
  module.
* `TauCeti.freeProfiniteGroup.abelianizationProPEquivRelationModule_smul`: Lyndon's isomorphism is
  equivariant for conjugation by `F ⧸ R` on `R^ab(p)` and multiplication by `π f` on the relation
  module.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Propositions (5.6.5) and (5.6.6).
* R. C. Lyndon, *Cohomology theory of groups with a single defining relation*, Ann. of Math. 52
  (1950).
* R. H. Fox, *Free differential calculus. I*, Ann. of Math. 57 (1953).
-/

public section

namespace TauCeti.freeProfiniteGroup

open _root_.MonoidAlgebra Multiplicative Additive

universe u

variable (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] {ι : Type u} (g : ι → G)

section Crossed

/-- Two continuous maps `c : F → G → N` that are crossed homomorphisms for left translation
through `lift g`, `c (f * f') x = c f x + c f' ((lift g f)⁻¹ * x)`, and agree on the generators
are equal: they are continuous `1`-cocycles of `F` with values in the coinduced module `G → N`. -/
private theorem eq_of_crossed {N : Type*} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [T1Space N]
    {c₁ c₂ : freeProfiniteGroup ι → G → N} (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (h₁ : ∀ f f' x, c₁ (f * f') x = c₁ f x + c₁ f' ((lift g f)⁻¹ * x))
    (h₂ : ∀ f f' x, c₂ (f * f') x = c₂ f x + c₂ f' ((lift g f)⁻¹ * x))
    (h : ∀ i, c₁ (of i) = c₂ (of i)) : c₁ = c₂ := by
  let : MulAction G (G → N) := arrowAction
  let : MulAction (freeProfiniteGroup ι) (G → N) := MulAction.compHom _ (lift g).toMonoidHom
  -- The action of `f` on `G → N` is translation by `(lift g f)⁻¹`, by definition of
  -- `arrowAction`.
  have hsmul : ∀ (f : freeProfiniteGroup ι) (φ : G → N) (x : G),
      (f • φ) x = φ ((lift g f)⁻¹ * x) :=
    fun _ _ _ ↦ rfl
  have hcoc : groupCohomology.IsCocycle₁ (c₁ - c₂) := fun f f' ↦ funext fun x ↦ by
    simp only [Pi.sub_apply, Pi.add_apply, hsmul, h₁, h₂]
    abel
  have htop :
      (Subgroup.closure (Set.range (of : ι → freeProfiniteGroup ι))).topologicalClosure = ⊤ :=
    Subgroup.coe_eq_univ.1 (by
      rw [Subgroup.topologicalClosure_coe]; exact (dense_closure_range_of ι).closure_eq)
  exact sub_eq_zero.1 (groupCohomology.eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top
    hcoc (hc₁.sub hc₂) htop (by rintro _ ⟨i, rfl⟩; simp [h i]))

end Crossed

section FoxDerivative

variable [DecidableEq ι]

/-- There is a continuous map `D : F → ℤ_p[G]^ι` with `D (f * f') = D f + lift g f • D f'` and
`D (of i) = e_i`. -/
private theorem exists_foxDerivative :
    ∃ D : freeProfiniteGroup ι → ι → MonoidAlgebra ℤ_[p] G,
      (Continuous fun f i x ↦ (D f i).coeff x) ∧
      (∀ f f', D (f * f') = D f + single (lift g f) (1 : ℤ_[p]) • D f') ∧
      ∀ i, D (of i) = Pi.single i 1 := by
  classical
  -- `D` is the coordinate of the continuous homomorphism from `F` to the semidirect product of
  -- `G` by `G → ℤ_p^ι` sending `of i` to `(e_i, g i)`. Here `G` acts on `G → ℤ_p^ι` by left
  -- translation; the semidirect product is the extension attached to the trivial factor set, and
  -- it is a profinite group.
  let : MulDistribMulAction G (G → Multiplicative (ι → ℤ_[p])) := arrowMulDistribMulAction
  have hsmul : ∀ (h : G) (φ : G → Multiplicative (ι → ℤ_[p])) (x : G),
      (h • φ) x = φ (h⁻¹ * x) :=
    fun _ _ _ ↦ rfl
  have : ContinuousSMul G (G → Multiplicative (ι → ℤ_[p])) :=
    ⟨continuous_prod_of_discrete_left.2 fun h ↦ continuous_pi fun x ↦ by
      simpa only [hsmul] using continuous_apply (h⁻¹ * x)⟩
  let α := FactorSet.trivial G (G → Multiplicative (ι → ℤ_[p]))
  have : IsTopologicalGroup α.Extension :=
    FactorSet.Extension.isTopologicalGroup FactorSet.continuous_trivial
  let Φ := lift (P := α.Extension) fun i ↦ ⟨Pi.mulSingle 1 (ofAdd (Pi.single i 1)), g i⟩
  have hright : ∀ f, (Φ f).right = lift g f := by
    have hcomp : (⟨FactorSet.rightHom α, FactorSet.continuous_rightHom α⟩ :
        α.Extension →ₜ* G).comp Φ = lift g :=
      hom_ext fun i ↦ by simp [Φ, lift_of, FactorSet.rightHom_apply]
    exact fun f ↦ by simpa [FactorSet.rightHom_apply] using DFunLike.congr_fun hcomp f
  refine ⟨fun f i ↦ ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ toAdd ((Φ f).left x) i),
    ?_, fun f f' ↦ ?_, fun i ↦ ?_⟩
  · simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact continuous_pi fun i ↦ continuous_pi fun x ↦ (continuous_apply i).comp
      (continuous_toAdd.comp ((continuous_apply x).comp
        (FactorSet.Extension.continuous_left.comp Φ.continuous)))
  · funext i
    refine coeff_injective (Finsupp.ext fun x ↦ ?_)
    simp [α, FactorSet.Extension.mul_left, hright, hsmul, FactorSet.trivial_apply]
  · funext j
    refine coeff_injective (Finsupp.ext fun x ↦ ?_)
    by_cases hx : x = 1 <;> by_cases hj : j = i <;>
      simp [Φ, lift_of, Pi.mulSingle_apply, one_def, hx, hj]

/-- **The Fox derivative along `lift g`**, read in `ℤ_p[G]`: the unique continuous map
`D : F → ℤ_p[G]^ι` with `D (f * f') = D f + lift g f • D f'` and `D (of i) = e_i`
(`foxDerivative_unique`). Its `i`-th coordinate is the image in `ℤ_p[G]` of the Fox derivative
`∂f/∂x_i` of `f`. -/
noncomputable def foxDerivative : freeProfiniteGroup ι → ι → MonoidAlgebra ℤ_[p] G :=
  (exists_foxDerivative p g).choose

/-- The coefficients of the Fox derivative depend continuously on the element of `F`. -/
theorem continuous_coeff_foxDerivative :
    Continuous fun f i x ↦ (foxDerivative p g f i).coeff x :=
  (exists_foxDerivative p g).choose_spec.1

/-- **The Leibniz rule of the Fox derivative**: `D (f * f') = D f + lift g f • D f'`. -/
theorem foxDerivative_mul (f f' : freeProfiniteGroup ι) :
    foxDerivative p g (f * f') =
      foxDerivative p g f + single (lift g f) (1 : ℤ_[p]) • foxDerivative p g f' :=
  (exists_foxDerivative p g).choose_spec.2.1 f f'

/-- The Fox derivative of the generator `of i` is the standard basis vector `e_i`. -/
@[simp]
theorem foxDerivative_of (i : ι) : foxDerivative p g (of i) = Pi.single i 1 :=
  (exists_foxDerivative p g).choose_spec.2.2 i

/-- The Fox derivative of `1` is `0`. -/
@[simp]
theorem foxDerivative_one : foxDerivative p g 1 = 0 := by
  have h := foxDerivative_mul p g 1 1
  rwa [mul_one, map_one, ← one_def, one_smul, left_eq_add] at h

/-- The Fox derivative of an inverse: `D f⁻¹ = -(lift g f)⁻¹ • D f`. -/
theorem foxDerivative_inv (f : freeProfiniteGroup ι) :
    foxDerivative p g f⁻¹ = -(single (lift g f)⁻¹ (1 : ℤ_[p]) • foxDerivative p g f) := by
  have h := foxDerivative_mul p g f⁻¹ f
  rw [inv_mul_cancel, foxDerivative_one, map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The Fox derivative of a quotient: `D (f * f'⁻¹) = D f - lift g (f * f'⁻¹) • D f'`. -/
theorem foxDerivative_mul_inv (f f' : freeProfiniteGroup ι) :
    foxDerivative p g (f * f'⁻¹) =
      foxDerivative p g f - single (lift g (f * f'⁻¹)) (1 : ℤ_[p]) • foxDerivative p g f' := by
  rw [eq_sub_iff_add_eq, ← foxDerivative_mul, inv_mul_cancel_right]

/-- On the kernel of `lift g` the Fox derivative is additive. -/
theorem foxDerivative_mul_of_mem_ker {r : freeProfiniteGroup ι}
    (hr : r ∈ (lift g : freeProfiniteGroup ι →* G).ker) (f : freeProfiniteGroup ι) :
    foxDerivative p g (r * f) = foxDerivative p g r + foxDerivative p g f := by
  have hr : lift g r = 1 := MonoidHom.mem_ker.1 hr
  rw [foxDerivative_mul, hr, ← one_def, one_smul]

/-- On the kernel of `lift g` the Fox derivative is equivariant for conjugation:
`D (f * r * f⁻¹) = lift g f • D r`. -/
theorem foxDerivative_conj {r : freeProfiniteGroup ι}
    (hr : r ∈ (lift g : freeProfiniteGroup ι →* G).ker) (f : freeProfiniteGroup ι) :
    foxDerivative p g (f * r * f⁻¹) = single (lift g f) (1 : ℤ_[p]) • foxDerivative p g r := by
  have hr : lift g r = 1 := MonoidHom.mem_ker.1 hr
  rw [foxDerivative_mul_inv, foxDerivative_mul]
  simp [hr, ← one_def]

/-- **The Fox derivative is unique**: a continuous map `D : F → ℤ_p[G]^ι` with
`D (f * f') = D f + lift g f • D f'` and `D (of i) = e_i` is `foxDerivative p g`. -/
theorem foxDerivative_unique (D : freeProfiniteGroup ι → ι → MonoidAlgebra ℤ_[p] G)
    (hD : Continuous fun f i x ↦ (D f i).coeff x)
    (hmul : ∀ f f', D (f * f') = D f + single (lift g f) (1 : ℤ_[p]) • D f')
    (hof : ∀ i, D (of i) = Pi.single i 1) : D = foxDerivative p g := by
  funext f i
  refine coeff_injective (Finsupp.ext fun x ↦ congrFun (congrFun (eq_of_crossed g
    (c₁ := fun f x ↦ (D f i).coeff x) (c₂ := fun f x ↦ (foxDerivative p g f i).coeff x)
    (continuous_pi fun x ↦ (continuous_apply x).comp ((continuous_apply i).comp hD))
    (continuous_pi fun x ↦ (continuous_apply x).comp
      ((continuous_apply i).comp (continuous_coeff_foxDerivative p g)))
    (fun f f' x ↦ by simp [hmul]) (fun f f' x ↦ by simp [foxDerivative_mul])
    (fun j ↦ by simp [hof])) f) x)

variable [Fintype ι]

/-- **The fundamental formula of Fox calculus**, read in `ℤ_p[G]`:
`∑ i, D f i * (g i - 1) = lift g f - 1`. -/
theorem sum_foxDerivative_mul_sub_one (f : freeProfiniteGroup ι) :
    ∑ i, foxDerivative p g f i * (single (g i) (1 : ℤ_[p]) - 1) = single (lift g f) 1 - 1 := by
  have key := eq_of_crossed g (N := ℤ_[p])
    (c₁ := fun f x ↦ (∑ i, foxDerivative p g f i * (single (g i) (1 : ℤ_[p]) - 1)).coeff x)
    (c₂ := fun f x ↦ (single (lift g f) (1 : ℤ_[p]) - 1).coeff x) ?_ ?_ ?_ ?_ ?_
  · exact coeff_injective (Finsupp.ext (congrFun (congrFun key f)))
  · -- The coefficients of the left side are finite sums of coefficients of `D f`.
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, coeff_sub, coeff_sum, Finsupp.sub_apply,
      Finsupp.finsetSum_apply, coeff_mul_single_apply]
    have hc : ∀ i y, Continuous fun f ↦ (foxDerivative p g f i).coeff y := fun i y ↦
      (continuous_apply y).comp ((continuous_apply i).comp (continuous_coeff_foxDerivative p g))
    exact continuous_pi fun x ↦ (continuous_finsetSum _ fun i _ ↦ hc i _).sub
      (continuous_finsetSum _ fun i _ ↦ hc i _)
  · exact continuous_pi fun x ↦ (continuous_of_discreteTopology
      (f := fun y : G ↦ (single y (1 : ℤ_[p]) - 1).coeff x)).comp (lift g).continuous
  · intro f f' x
    simp [foxDerivative_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  · intro f f' x
    have : single (lift g (f * f')) (1 : ℤ_[p]) - 1 = (single (lift g f) 1 - 1) +
        single (lift g f) 1 * (single (lift g f') 1 - 1) := by
      rw [mul_sub, single_mul_single, mul_one, map_mul, mul_one]
      abel
    rw [this]
    simp
  · intro i
    funext x
    simp [Pi.single_apply, lift_of]

/-- The Fox derivative maps the kernel of `lift g` into the relation module of `g`. -/
theorem foxDerivative_mem_relationModule {r : freeProfiniteGroup ι}
    (hr : r ∈ (lift g : freeProfiniteGroup ι →* G).ker) :
    foxDerivative p g r ∈ MonoidAlgebra.relationModule ℤ_[p] G g := by
  have hr : lift g r = 1 := MonoidHom.mem_ker.1 hr
  rw [MonoidAlgebra.mem_relationModule_iff, sum_foxDerivative_mul_sub_one, hr, ← one_def,
    sub_self]

end FoxDerivative

section Lyndon

variable {g}

/-- The kernel of `lift g` is compact, so that `R^ab(p)` is a profinite pro-`p` group. -/
private instance compactSpace_ker : CompactSpace (lift g : freeProfiniteGroup ι →* G).ker :=
  isCompact_iff_compactSpace.mp (isClosed_singleton.preimage (lift g).continuous).isCompact

variable (hg : Subgroup.closure (Set.range g) = ⊤)

open scoped Classical in
/-- A section of `lift g`, normalized to send `1` to `1`. -/
private noncomputable def sec : G → freeProfiniteGroup ι :=
  Function.update (Function.surjInv (lift_surjective (f := g) (by
    rw [hg, Subgroup.coe_top]; exact dense_univ))) 1 1

open scoped Classical in
private theorem sec_one : sec hg 1 = 1 :=
  Function.update_self _ _ _

open scoped Classical in
private theorem lift_sec (x : G) : lift g (sec hg x) = x := by
  by_cases hx : x = 1
  · subst hx; rw [sec_one, map_one]
  · rw [sec, Function.update_of_ne hx]
    exact Function.surjInv_eq _ x

/-- The element `a * s (lift g a)⁻¹` of the kernel, for the section `s = sec hg`. -/
private noncomputable def toKer (a : freeProfiniteGroup ι) :
    (lift g : freeProfiniteGroup ι →* G).ker :=
  ⟨a * (sec hg (lift g a))⁻¹, by simp [MonoidHom.mem_ker, lift_sec]⟩

private theorem toKer_mul (a b : freeProfiniteGroup ι) :
    toKer hg (a * b) = toKer hg a * toKer hg (sec hg (lift g a) * b) :=
  Subtype.ext (by simp [toKer, lift_sec, mul_assoc])

private theorem continuous_toKer : Continuous (toKer hg) :=
  (continuous_id.mul ((continuous_of_discreteTopology (f := fun y ↦ (sec hg y)⁻¹)).comp
    (lift g).continuous)).subtype_mk _

/-- The crossed homomorphism `f ↦ (x ↦ [s x⁻¹ * f * s (x⁻¹ * lift g f)⁻¹])` of `F` with values in
the coinduced module `G → R^ab(p)`, for the section `s = sec hg`. -/
private noncomputable def schreierCocycle (f : freeProfiniteGroup ι) (x : G) :
    Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) :=
  ofMul (abelianizationProPMk p _ _ (toKer hg (sec hg x⁻¹ * f)))

omit [Fact p.Prime] in
private theorem schreierCocycle_mul (f f' : freeProfiniteGroup ι) (x : G) :
    schreierCocycle p hg (f * f') x =
      schreierCocycle p hg f x + schreierCocycle p hg f' ((lift g f)⁻¹ * x) := by
  simp only [schreierCocycle, ← mul_assoc, toKer_mul hg (sec hg x⁻¹ * f), map_mul, lift_sec,
    mul_inv_rev, inv_inv, ofMul_mul]

omit [Fact p.Prime] in
private theorem continuous_schreierCocycle : Continuous (schreierCocycle p hg) :=
  continuous_pi fun _ ↦ continuous_ofMul.comp ((continuous_abelianizationProPMk p _ _).comp
    ((continuous_toKer hg).comp (continuous_const.mul continuous_id)))

/-- The Schreier element of `R` at `1 ∈ G` and `r ∈ R` is `r` itself. -/
private theorem toKer_sec_one_mul (r : (lift g : freeProfiniteGroup ι →* G).ker) :
    toKer hg (sec hg 1⁻¹ * r) = r := by
  have hr : lift g r = 1 := MonoidHom.mem_ker.1 r.2
  exact Subtype.ext (by simp [toKer, sec_one, hr])

variable [DecidableEq ι]

private theorem foxDerivative_toKer (a : freeProfiniteGroup ι) :
    foxDerivative p g (toKer hg a) =
      foxDerivative p g a - foxDerivative p g (sec hg (lift g a)) := by
  simp [toKer, foxDerivative_mul_inv, lift_sec, ← one_def]

/-! ### The Fox derivative on `R^ab(p)` -/

/-- The Fox derivative on the kernel, as a homomorphism to the coefficient vectors. -/
private noncomputable def foxHom :
    (lift g : freeProfiniteGroup ι →* G).ker →* Multiplicative (ι × G → ℤ_[p]) where
  toFun r := ofAdd fun k ↦ (foxDerivative p g r k.1).coeff k.2
  map_one' := by simp; rfl
  map_mul' r r' := by
    simp only [Subgroup.coe_mul, foxDerivative_mul_of_mem_ker p g r.2, ← ofAdd_add]
    congr 1

private theorem continuous_foxHom : Continuous (foxHom p (g := g)) :=
  continuous_ofAdd.comp (continuous_pi fun k ↦ (continuous_apply k.2).comp
    ((continuous_apply k.1).comp
      ((continuous_coeff_foxDerivative p g).comp continuous_subtype_val)))

/-- The Fox derivative factors through `R^ab(p)`. -/
private noncomputable def abelianFoxHom :
    abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker →*
      Multiplicative (ι × G → ℤ_[p]) :=
  maximalProPQuotient.lift (isProP_multiplicative_pi_padicInt p (ι × G))
    (QuotientGroup.lift _ (foxHom p) (Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker _)
      (isClosed_singleton.preimage (continuous_foxHom p))))
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_foxHom p))

private theorem continuous_abelianFoxHom : Continuous (abelianFoxHom p (g := g)) :=
  maximalProPQuotient.continuous_lift _ _ _

private theorem abelianFoxHom_mk (r : (lift g : freeProfiniteGroup ι →* G).ker) :
    abelianFoxHom p (abelianizationProPMk p _ _ r) = foxHom p r := by
  rw [abelianizationProPMk_apply, abelianFoxHom, maximalProPQuotient.mk_apply,
    maximalProPQuotient.lift_mk, QuotientGroup.lift_mk]

/-- The Fox derivative on `R^ab(p)`, read in `ℤ_p[G]^ι`. -/
private noncomputable def foxAddHom :
    Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) →+
      (ι → MonoidAlgebra ℤ_[p] G) where
  toFun a i :=
    ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ toAdd (abelianFoxHom p a.toMul) (i, x))
  map_zero' := by
    funext i
    exact coeff_injective (Finsupp.ext fun x ↦ by simp)
  map_add' a b := by
    funext i
    exact coeff_injective (Finsupp.ext fun x ↦ by simp)

private theorem foxAddHom_ofMul_mk (r : (lift g : freeProfiniteGroup ι →* G).ker) :
    foxAddHom p (ofMul (abelianizationProPMk p _ _ r)) = foxDerivative p g r := by
  funext i
  refine coeff_injective (Finsupp.ext fun x ↦ ?_)
  simp only [foxAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, abelianFoxHom_mk]
  simp [foxHom]

private theorem foxAddHom_padicPow
    (a : abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) (c : ℤ_[p]) :
    foxAddHom p (ofMul (isProP_maximalProPQuotient.padicPow a c)) =
      c • foxAddHom p (ofMul a) := by
  have h := isProP_maximalProPQuotient.map_padicPow (isProP_multiplicative_pi_padicInt p (ι × G))
    (abelianFoxHom p) (continuous_abelianFoxHom p) a c
  rw [← ofAdd_toAdd (abelianFoxHom p a), IsProP.padicPow_ofAdd_pi] at h
  funext i
  exact coeff_injective (Finsupp.ext fun x ↦ by simp [foxAddHom, h])

variable [Fintype ι]

private theorem foxAddHom_mem
    (a : Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker)) :
    foxAddHom p a ∈ MonoidAlgebra.relationModule ℤ_[p] G g := by
  obtain ⟨r, hr⟩ := abelianizationProPMk_surjective p _ _ a.toMul
  rw [← ofMul_toMul a, ← hr, foxAddHom_ofMul_mk]
  exact foxDerivative_mem_relationModule p g r.2

/-! ### The Schreier inverse -/

/-- The inverse of the Fox derivative, written on the Schreier generators:
`m ↦ ∑ (m i)(h) • [s (x⁻¹ * h) * of i * s (x⁻¹ * h * g i)⁻¹]`. At `x = 1` it inverts the Fox
derivative on the relation module; as a function of `x` it is the crossed homomorphism
`schreierCocycle` read off the Fox derivative. -/
private noncomputable def schreierSum (m : ι → MonoidAlgebra ℤ_[p] G) (x : G) :
    Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) :=
  ∑ i, (m i).coeff.sum fun h c ↦ ofMul (isProP_maximalProPQuotient.padicPow
    (abelianizationProPMk p _ _ (toKer hg (sec hg (x⁻¹ * h) * of i))) c)

omit [DecidableEq ι] in
private theorem schreierSum_eq [Fintype G] (m : ι → MonoidAlgebra ℤ_[p] G) (x : G) :
    schreierSum p hg m x = ∑ i, ∑ h, ofMul (isProP_maximalProPQuotient.padicPow
      (abelianizationProPMk p _ _ (toKer hg (sec hg (x⁻¹ * h) * of i))) ((m i).coeff h)) :=
  Finset.sum_congr rfl fun _ _ ↦ Finsupp.sum_fintype _ _ fun _ ↦ by simp

omit [DecidableEq ι] in
private theorem schreierSum_add (m m' : ι → MonoidAlgebra ℤ_[p] G) (x : G) :
    schreierSum p hg (m + m') x = schreierSum p hg m x + schreierSum p hg m' x := by
  have := Fintype.ofFinite G
  simp [schreierSum_eq, IsProP.padicPow_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
private theorem schreierSum_single_smul (y : G) (m : ι → MonoidAlgebra ℤ_[p] G) (x : G) :
    schreierSum p hg (single y (1 : ℤ_[p]) • m) x = schreierSum p hg m (y⁻¹ * x) := by
  have := Fintype.ofFinite G
  simp only [schreierSum_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp [mul_assoc]

private theorem schreierSum_single (i : ι) (x : G) :
    schreierSum p hg (Pi.single i 1) x = schreierCocycle p hg (of i) x := by
  rw [schreierSum, Fintype.sum_eq_single i fun j hj ↦ by simp [hj]]
  simp [one_def, Finsupp.sum_single_index, IsProP.padicPow_one, schreierCocycle]

private theorem continuous_schreierSum_foxDerivative :
    Continuous fun f x ↦ schreierSum p hg (foxDerivative p g f) x := by
  have := Fintype.ofFinite G
  simp only [schreierSum_eq]
  have hc : ∀ i h, Continuous fun f ↦ (foxDerivative p g f i).coeff h := fun i h ↦
    (continuous_apply h).comp ((continuous_apply i).comp (continuous_coeff_foxDerivative p g))
  exact continuous_pi fun x ↦ continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun h _ ↦
    continuous_ofMul.comp (isProP_maximalProPQuotient.continuous_padicPow.comp
      ((hc i h).prodMk continuous_const))

/-- The crossed homomorphism `schreierCocycle` is read off the Fox derivative, since both sides
are continuous crossed homomorphisms with the same values on the generators. -/
private theorem schreierCocycle_eq_schreierSum :
    schreierCocycle p hg = fun f x ↦ schreierSum p hg (foxDerivative p g f) x :=
  eq_of_crossed g (continuous_schreierCocycle p hg) (continuous_schreierSum_foxDerivative p hg)
    (schreierCocycle_mul p hg)
    (fun f f' x ↦ by simp only [foxDerivative_mul, schreierSum_add, schreierSum_single_smul])
    (fun i ↦ funext fun x ↦ by simp only [foxDerivative_of, schreierSum_single])

/-- The Schreier sum is a left inverse of the Fox derivative on `R`. -/
private theorem schreierSum_foxDerivative (r : (lift g : freeProfiniteGroup ι →* G).ker) :
    schreierSum p hg (foxDerivative p g r) 1 = ofMul (abelianizationProPMk p _ _ r) := by
  have h := congrFun (congrFun (schreierCocycle_eq_schreierSum p hg) r) 1
  rw [← h, schreierCocycle, toKer_sec_one_mul]

omit [Fintype ι] in
/-- The Fox derivative of the Schreier element at `h` and `i` is
`D (s h) + h • e_i - D (s (h * g i))`. -/
private theorem foxDerivative_toKer_sec_mul_of (h : G) (i : ι) :
    foxDerivative p g (toKer hg (sec hg h * of i)) = foxDerivative p g (sec hg h) +
      Pi.single i (single h 1) - foxDerivative p g (sec hg (h * g i)) := by
  rw [foxDerivative_toKer, foxDerivative_mul, foxDerivative_of, map_mul, lift_sec, lift_of]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- **The Schreier elements span the relation module**: an element `m` of the relation module is
`∑ (m i)(h) • D (s h * of i * s (h * g i)⁻¹)`. The terms `D (s h)` cancel by the relation
`∑ m i * (g i - 1) = 0`. -/
private theorem sum_smul_foxDerivative_toKer [Fintype G] {m : ι → MonoidAlgebra ℤ_[p] G}
    (hm : m ∈ MonoidAlgebra.relationModule ℤ_[p] G g) :
    ∑ i, ∑ h, (m i).coeff h • foxDerivative p g (toKer hg (sec hg h * of i)) = m := by
  have hrel : ∀ k, ∑ i, (m i).coeff (k * (g i)⁻¹) = ∑ i, (m i).coeff k := fun k ↦ by
    have := congrArg (fun y ↦ y.coeff k) (MonoidAlgebra.mem_relationModule_iff.1 hm)
    simpa [mul_sub, coeff_sum, Finsupp.finsetSum_apply, Finset.sum_sub_distrib, sub_eq_zero]
      using this
  have hB : ∑ i, ∑ h, (m i).coeff h • (Pi.single i (single h 1) : ι → MonoidAlgebra ℤ_[p] G) =
      m := by
    funext j
    conv_rhs => rw [← sum_coeff_single (m j), Finsupp.sum_fintype _ _ (by simp)]
    simp [Finset.sum_apply, Pi.single_apply]
  have hC : ∑ i, ∑ h, (m i).coeff h • foxDerivative p g (sec hg (h * g i)) =
      ∑ i, ∑ h, (m i).coeff h • foxDerivative p g (sec hg h) := by
    calc _ = ∑ i, ∑ h, (m i).coeff (h * (g i)⁻¹) • foxDerivative p g (sec hg h) :=
          Finset.sum_congr rfl fun i _ ↦ by
            rw [← Equiv.sum_comp (Equiv.mulRight (g i)⁻¹)]; simp
      _ = ∑ h, (∑ i, (m i).coeff (h * (g i)⁻¹)) • foxDerivative p g (sec hg h) := by
          rw [Finset.sum_comm]; simp [Finset.sum_smul]
      _ = _ := by
          simp only [hrel, Finset.sum_smul]; rw [Finset.sum_comm]
  simp only [foxDerivative_toKer_sec_mul_of, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hB, hC]
  abel

/-- The Schreier sum is a right inverse of the Fox derivative on the relation module. -/
private theorem foxAddHom_schreierSum {m : ι → MonoidAlgebra ℤ_[p] G}
    (hm : m ∈ MonoidAlgebra.relationModule ℤ_[p] G g) : foxAddHom p (schreierSum p hg m 1) = m := by
  have := Fintype.ofFinite G
  simp only [schreierSum_eq, map_sum, foxAddHom_padicPow, foxAddHom_ofMul_mk, inv_one, one_mul]
  exact sum_smul_foxDerivative_toKer p hg hm

/-! ### Lyndon's isomorphism -/

/-- **Lyndon's theorem for the relation module** (NSW (5.6.6)). For a finite group `G` generated by
the family `g : ι → G`, the maximal abelian pro-`p` quotient `R^ab(p)` of the kernel `R` of
`lift g : F → G` is isomorphic to the relation module `relationModule ℤ_[p] G g`. The isomorphism
sends the class of `r ∈ R` to its Fox derivative
(`coe_abelianizationProPEquivRelationModule_ofMul`), it is `ℤ_p`-linear
(`abelianizationProPEquivRelationModule_padicPow`), and it is equivariant
(`abelianizationProPEquivRelationModule_smul`). -/
noncomputable def abelianizationProPEquivRelationModule :
    Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) ≃+
      MonoidAlgebra.relationModule ℤ_[p] G g where
  toFun a := ⟨foxAddHom p a, foxAddHom_mem p a⟩
  invFun m := schreierSum p hg m 1
  left_inv a := by
    obtain ⟨r, hr⟩ := abelianizationProPMk_surjective p _ _ a.toMul
    rw [← ofMul_toMul a, ← hr]
    dsimp only
    rw [foxAddHom_ofMul_mk, schreierSum_foxDerivative]
  right_inv m := Subtype.ext (foxAddHom_schreierSum p hg m.2)
  map_add' a b := Subtype.ext (map_add (foxAddHom p) a b)

/-- Lyndon's isomorphism sends the class of `r ∈ R` to the Fox derivative of `r`. -/
@[simp]
theorem coe_abelianizationProPEquivRelationModule_ofMul
    (r : (lift g : freeProfiniteGroup ι →* G).ker) :
    (abelianizationProPEquivRelationModule p hg (ofMul (abelianizationProPMk p _ _ r)) :
      ι → MonoidAlgebra ℤ_[p] G) = foxDerivative p g r :=
  foxAddHom_ofMul_mk p r

/-- Lyndon's isomorphism is `ℤ_p`-linear: it sends the `p`-adic power `a ^ c` in `R^ab(p)` to
`c` times the image of `a`. -/
@[simp]
theorem abelianizationProPEquivRelationModule_padicPow
    (a : abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker) (c : ℤ_[p]) :
    haveI : CompactSpace (lift g : freeProfiniteGroup ι →* G).ker :=
      isCompact_iff_compactSpace.mp (isClosed_singleton.preimage (lift g).continuous).isCompact
    abelianizationProPEquivRelationModule p hg (ofMul (isProP_maximalProPQuotient.padicPow a c)) =
      c • abelianizationProPEquivRelationModule p hg (ofMul a) :=
  Subtype.ext (foxAddHom_padicPow p a c)

/-- **Lyndon's isomorphism is equivariant**: conjugation by `f ∈ F` on `R^ab(p)`, through
`F ⧸ R`, corresponds to multiplication by `lift g f` on the relation module. -/
theorem abelianizationProPEquivRelationModule_smul (f : freeProfiniteGroup ι)
    (x : Additive (abelianizationProP p _ (lift g : freeProfiniteGroup ι →* G).ker)) :
    abelianizationProPEquivRelationModule p hg
        ((f : freeProfiniteGroup ι ⧸ (lift g : freeProfiniteGroup ι →* G).ker) • x) =
      single (lift g f) (1 : ℤ_[p]) • abelianizationProPEquivRelationModule p hg x := by
  obtain ⟨r, hr⟩ := abelianizationProPMk_surjective p _ _ x.toMul
  rw [← ofMul_toMul x, ← hr, ← ofMul_smul, abelianizationProPMk_conj]
  ext1
  rw [Submodule.coe_smul, coe_abelianizationProPEquivRelationModule_ofMul,
    coe_abelianizationProPEquivRelationModule_ofMul, MulAut.conjNormal_apply,
    foxDerivative_conj p g r.2]

end Lyndon

end TauCeti.freeProfiniteGroup
