/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.Category.CommAlgCat.PowerSeries
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Smooth.AdicCompletion
import TauCeti.Algebra.AlgebraicGroup.Trivial
import TauCeti.RingTheory.AdicCompletion.Pow

/-!
# Formal loop groups and their congruence subgroups

Let `G` be the affine group over a commutative ring `k` with coordinate Hopf algebra `H`, with
points `G(A) = WithConv (H →ₐ[k] A)` (`TauCeti.HopfAlgebra.points`). For a commutative
`k`-algebra `R`, the **formal loop group** and the **positive formal loop group** of `G` are

  `LG(R) = G(R⸨t⸩)`, `L⁺G(R) = G(R⟦t⟧)`,

the points of `G` on the punctured formal disc and on the formal disc over `R`. Both are group
functors of `R` on all commutative `k`-algebras, nonreduced ones included, and contravariant
functors of `H`; the inclusion `R⟦t⟧ → R⸨t⸩` induces an injective natural homomorphism
`L⁺G → LG`. Here `R⸨t⸩` carries its coefficientwise `k`-algebra structure, as in
`CommAlgCat.laurentSeries`.

For `N : ℕ` the **congruence subgroup** `K_N(R) ⊆ L⁺G(R)` is the kernel of reduction modulo
`t ^ N`, the principal congruence subgroup `TauCeti.HopfAlgebra.congruenceSubgroup` of `G(R⟦t⟧)`
for the ideal `(t ^ N)`. These form a decreasing sequence of normal subgroups of `L⁺G(R)`,
natural in `R`, with trivial intersection. Reduction modulo `t ^ N` embeds `L⁺G(R) / K_N(R)` into
the group `G(R⟦t⟧ ⧸ (t ^ N))` of points on the truncated disc `R⟦t⟧ ⧸ (t ^ N) ≅ R[t] ⧸ (t ^ N)`,
and when `H` is formally smooth over `k` the embedding is onto, because `R⟦t⟧` is `t`-adically
complete. For the trivial group all these groups are trivial.

## Main definitions

* `TauCeti.HopfAlgebra.loopGroup k H`: the formal loop group `LG`, a functor
  `CommAlgCat k ⥤ GrpCat`.
* `TauCeti.HopfAlgebra.positiveLoopGroup k H`: the positive formal loop group `L⁺G`.
* `TauCeti.HopfAlgebra.positiveLoopToLoop k H`: the natural homomorphism `L⁺G → LG`, injective
  at every `R` (`positiveLoopToLoop_app_injective`).
* `TauCeti.CommHopfAlgCat.loopGroupFunctor k`, `TauCeti.CommHopfAlgCat.positiveLoopGroupFunctor k`
  and `TauCeti.CommHopfAlgCat.positiveLoopToLoop k`: the same, as functors and a natural
  transformation in both the commutative Hopf algebra and the coefficient algebra.
* `TauCeti.HopfAlgebra.congruenceLoopGroup k H N`: the congruence subgroup functor `K_N`, with
  its inclusion `congruenceLoopGroupIncl` into `L⁺G`.

## Main results

* `TauCeti.HopfAlgebra.congruenceSubgroup_span_X_pow_antitone`: `K_M(R) ⊆ K_N(R)` for `N ≤ M`.
* `TauCeti.HopfAlgebra.iInf_congruenceSubgroup_span_X_pow`: `⋂ N, K_N(R) = 1`.
* `TauCeti.HopfAlgebra.mkₐ_span_X_pow_comp_surjective`: for formally smooth `H`, every point of
  `G(R⟦t⟧ ⧸ (t ^ N))` lifts to `L⁺G(R)`.
* `TauCeti.HopfAlgebra.quotientCongruenceSubgroupHom_span_X_pow_bijective`: for formally smooth
  `H`, reduction modulo `t ^ N` is an isomorphism `L⁺G(R) / K_N(R) ≅ G(R⟦t⟧ ⧸ (t ^ N))`; for
  every `H` it is injective (`quotientCongruenceSubgroupHom_injective`).

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Stud. Adv. Math. 103 (2007),
  §1.3.1, (1.3-1), p. 19.
-/

public section

open CategoryTheory Opposite WithConv PowerSeries

universe u v w

-- The coefficientwise `k`-algebra structure on Laurent series, as in `CommAlgCat.laurentSeries`.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti

namespace HopfAlgebra

section LoopGroups

variable (k : Type u) [CommRing k] (H : Type v) [Semiring H] [_root_.HopfAlgebra k H]

/-- The **formal loop group** `LG` of the affine group with coordinate Hopf algebra `H`: the
group functor `R ↦ G(R⸨t⸩)` of points on the punctured formal disc, on commutative
`k`-algebras `R`. -/
noncomputable abbrev loopGroup : CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  CommAlgCat.laurentSeries k ⋙ pointsFunctor (H := H)

/-- The **positive formal loop group** `L⁺G` of the affine group with coordinate Hopf algebra
`H`: the group functor `R ↦ G(R⟦t⟧)` of points on the formal disc, on commutative
`k`-algebras `R`. -/
noncomputable abbrev positiveLoopGroup : CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  CommAlgCat.powerSeries k ⋙ pointsFunctor (H := H)

/-- The group `LG(R)` is the group of points of `H` in `R⸨t⸩`. -/
lemma loopGroup_obj (R : CommAlgCat.{w} k) :
    (loopGroup k H).obj R = points (H := H) (CommAlgCat.of k (LaurentSeries R)) :=
  (rfl)

/-- The group `L⁺G(R)` is the group of points of `H` in `R⟦t⟧`. -/
lemma positiveLoopGroup_obj (R : CommAlgCat.{w} k) :
    (positiveLoopGroup k H).obj R = points (H := H) (CommAlgCat.of k (PowerSeries R)) :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on loops by applying `f` to the coefficients of their values. -/
lemma loopGroup_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S) (g : (loopGroup k H).obj R) :
    (loopGroup k H).map f g = AlgHom.mapValue (HahnSeries.mapAlgHom f.hom) g :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on positive loops by applying `f` to the coefficients of their
values. -/
lemma positiveLoopGroup_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (g : (positiveLoopGroup k H).obj R) :
    (positiveLoopGroup k H).map f g = AlgHom.mapValue (PowerSeries.mapAlgHom f.hom) g :=
  (rfl)

/-- The natural homomorphism `L⁺G → LG` induced by the inclusion `R⟦t⟧ → R⸨t⸩`. -/
noncomputable def positiveLoopToLoop : positiveLoopGroup.{u, v, w} k H ⟶ loopGroup k H :=
  Functor.whiskerRight (CommAlgCat.ofPowerSeries k) (pointsFunctor (H := H))

/-- The homomorphism `L⁺G(R) → LG(R)` composes a positive loop with `R⟦t⟧ → R⸨t⸩`. -/
lemma positiveLoopToLoop_app_apply (R : CommAlgCat.{w} k) (g : (positiveLoopGroup k H).obj R) :
    (positiveLoopToLoop k H).app R g = AlgHom.mapValue (HahnSeries.ofPowerSeriesAlg ℤ k) g :=
  -- The component of the whiskered transformation is `mapPoints` of the inclusion.
  (mapPoints_apply ((CommAlgCat.ofPowerSeries k).app R) g).trans <| by
    rw [CommAlgCat.ofPowerSeries_app_hom]
    exact (AlgHom.mapValue_apply _ g).symm

/-- A positive loop is determined by the loop it defines. -/
theorem positiveLoopToLoop_app_injective (R : CommAlgCat.{w} k) :
    Function.Injective ((positiveLoopToLoop k H).app R) :=
  AlgHom.mapValue_injective (CommAlgCat.ofPowerSeries_app_injective k R)

end LoopGroups

section CongruenceSubgroups

variable {k : Type u} [CommRing k] {H : Type v} [Semiring H] [_root_.HopfAlgebra k H]
  (R : Type w) [CommRing R] [Algebra k R]

variable (k H) in
/-- The congruence subgroups `K_N(R)` of `L⁺G(R)` decrease with `N`: `K_M(R) ⊆ K_N(R)` for
`N ≤ M`. -/
theorem congruenceSubgroup_span_X_pow_antitone :
    Antitone fun N : ℕ ↦ congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) :=
  fun _ _ hNM ↦ congruenceSubgroup_mono k H R⟦X⟧
    (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (X : R⟦X⟧) hNM))

variable (k H) in
/-- **Separation of the congruence filtration.** The congruence subgroups `K_N(R)` of `L⁺G(R)`
intersect trivially: a positive loop congruent to `1` modulo every `t ^ N` is `1`. -/
theorem iInf_congruenceSubgroup_span_X_pow :
    ⨅ N : ℕ, congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) = ⊥ := by
  -- `R⟦t⟧` is `t`-adically Hausdorff, so the ideals `(t ^ N)` intersect in `0`.
  have h := (inferInstance : IsHausdorff (Ideal.span {(X : R⟦X⟧)}) R⟦X⟧).iInf_pow_smul
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at h
  rw [← congruenceSubgroup_iInf, h, congruenceSubgroup_bot]

variable {R} in
/-- A coefficient map `f : R →ₐ[k] S` carries `K_N(R)` into `K_N(S)`. -/
theorem congruenceSubgroup_span_X_pow_le_comap_mapValue {S : Type*} [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) (N : ℕ) :
    congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}) ≤
      (congruenceSubgroup k H (Ideal.span {(X : S⟦X⟧) ^ N})).comap
        (AlgHom.mapValue (H := H) (PowerSeries.mapAlgHom f)) := by
  refine congruenceSubgroup_le_comap_mapValue _ ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, PowerSeries.mapAlgHom_apply,
    map_X]
  exact Ideal.mem_span_singleton_self _

variable (k H) in
/-- The **congruence subgroup functor** `K_N`: the group functor `R ↦ K_N(R)` of positive loops
congruent to `1` modulo `t ^ N`, on commutative `k`-algebras `R`. -/
@[expose] noncomputable def congruenceLoopGroup (N : ℕ) : CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}))
  map {R S} f := GrpCat.ofHom
    (((AlgHom.mapValue (H := H) (PowerSeries.mapAlgHom f.hom)).domRestrict
      (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N}))).codRestrict
        (congruenceSubgroup k H (Ideal.span {(X : S⟦X⟧) ^ N}))
      fun g ↦ congruenceSubgroup_span_X_pow_le_comap_mapValue f.hom N g.property)
  map_id R := GrpCat.ext fun g ↦ Subtype.ext <| WithConv.ext <| AlgHom.ext fun h ↦
    PowerSeries.ext fun n ↦ by simp [AlgHom.mapValue_apply, PowerSeries.mapAlgHom_apply]
  map_comp f g := GrpCat.ext fun x ↦ Subtype.ext <| by
    have key : AlgHom.mapValue (H := H) (PowerSeries.mapAlgHom (f ≫ g).hom) =
        (AlgHom.mapValue (PowerSeries.mapAlgHom g.hom)).comp
          (AlgHom.mapValue (PowerSeries.mapAlgHom f.hom)) := by
      rw [← AlgHom.mapValue_comp]
      exact congrArg _ (congrArg CommAlgCat.Hom.hom ((CommAlgCat.powerSeries k).map_comp f g))
    exact DFunLike.congr_fun key x.val

/-- The group `K_N(R)` is the congruence subgroup of `G(R⟦t⟧)` of level `(t ^ N)`. -/
lemma congruenceLoopGroup_obj (N : ℕ) (R : CommAlgCat.{w} k) :
    (congruenceLoopGroup k H N).obj R =
      GrpCat.of (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N})) :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on `K_N` by applying `f` to the coefficients of the values of a
positive loop. -/
@[simp]
lemma congruenceLoopGroup_map_apply (N : ℕ) {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (g : (congruenceLoopGroup k H N).obj R) :
    Subtype.val ((congruenceLoopGroup k H N).map f g) =
      AlgHom.mapValue (PowerSeries.mapAlgHom f.hom) (Subtype.val g) :=
  (rfl)

variable (k H) in
/-- The natural inclusion `K_N → L⁺G`. -/
noncomputable def congruenceLoopGroupIncl (N : ℕ) :
    congruenceLoopGroup.{u, v, w} k H N ⟶ positiveLoopGroup k H where
  app _ := GrpCat.ofHom (Subgroup.subtype _)
  naturality _ _ _ := rfl

/-- The component of `congruenceLoopGroupIncl` at `R` is the subgroup inclusion. -/
@[simp]
lemma congruenceLoopGroupIncl_app (N : ℕ) (R : CommAlgCat.{w} k) :
    (congruenceLoopGroupIncl k H N).app R =
      GrpCat.ofHom (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧) ^ N})).subtype :=
  (rfl)

end CongruenceSubgroups

section Jets

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]
  (R : Type w) [CommRing R] [Algebra k R]

variable (H) in
/-- **Lifting jets of formally smooth groups.** If `H` is formally smooth over `k`, every point of
`G(R⟦t⟧ ⧸ (t ^ N))` lifts to a positive loop in `G(R⟦t⟧)`: `R⟦t⟧` is complete for the ideal
`(t ^ N) = (t) ^ N`. -/
theorem mkₐ_span_X_pow_comp_surjective [Algebra.FormallySmooth k H] (N : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mkₐ k (Ideal.span {(X : R⟦X⟧) ^ N})).comp :
        (H →ₐ[k] R⟦X⟧) → H →ₐ[k] R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧) ^ N}) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- The quotient by `(t ^ 0) = ⊤` is the zero ring, which has a single point.
    have : Subsingleton (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧) ^ 0}) := by
      rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
    exact fun y ↦ ⟨(1 : WithConv (H →ₐ[k] R⟦X⟧)).ofConv,
      AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩
  · have : IsAdicComplete (Ideal.span {(X : R⟦X⟧) ^ N}) R⟦X⟧ := by
      rw [← Ideal.span_singleton_pow]
      exact IsAdicComplete.pow hN.ne'
    exact Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete

/-- **Positive loops modulo `K_N` are jets.** If `H` is formally smooth over `k`, reduction modulo
`t ^ N` is an isomorphism `L⁺G(R) / K_N(R) ≅ G(R⟦t⟧ ⧸ (t ^ N))`; the corresponding
multiplicative equivalence is `quotientCongruenceSubgroupEquiv` applied to
`mkₐ_span_X_pow_comp_surjective`. Without smoothness the map is still injective,
`quotientCongruenceSubgroupHom_injective`. -/
theorem quotientCongruenceSubgroupHom_span_X_pow_bijective [Algebra.FormallySmooth k H]
    (N : ℕ) :
    Function.Bijective
      (quotientCongruenceSubgroupHom k H (Ideal.span {(X : R⟦X⟧) ^ N})) :=
  ⟨quotientCongruenceSubgroupHom_injective _,
    quotientCongruenceSubgroupHom_surjective (mkₐ_span_X_pow_comp_surjective H R N)⟩

end Jets

section TrivialGroup

variable (k : Type u) [CommRing k]

/-- For the trivial group `G = 1`, with coordinate Hopf algebra `k`, the loop group is trivial. -/
noncomputable example (R : CommAlgCat.{w} k) : (loopGroup k k).obj R ≃* PUnit.{1} :=
  TrivialGroup.pointsMulEquiv

/-- For the trivial group, the positive loop group is trivial. -/
noncomputable example (R : CommAlgCat.{w} k) : (positiveLoopGroup k k).obj R ≃* PUnit.{1} :=
  TrivialGroup.pointsMulEquiv

/-- For the trivial group, every congruence subgroup is the whole positive loop group. -/
example (R : Type w) [CommRing R] [Algebra k R] (N : ℕ) :
    congruenceSubgroup k k (Ideal.span {(X : R⟦X⟧) ^ N}) = ⊤ :=
  eq_top_iff.2 fun g _ ↦ (WithConv.convPoint_eq_one g).symm ▸ one_mem _

end TrivialGroup

end HopfAlgebra

namespace CommHopfAlgCat

variable (k : Type u) [CommRing k]

/-- The formal loop group as a functor of the commutative Hopf algebra `H` and of the
coefficient algebra `R`: `(H, R) ↦ LG(R) = G(R⸨t⸩)`, contravariant in `H`. -/
@[expose] noncomputable def loopGroupFunctor :
    (_root_.CommHopfAlgCat.{v} k)ᵒᵖ ⥤ CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  pointsFunctor ⋙ (Functor.whiskeringLeft _ _ _).obj (CommAlgCat.laurentSeries k)

/-- The positive formal loop group as a functor of the commutative Hopf algebra `H` and of the
coefficient algebra `R`: `(H, R) ↦ L⁺G(R) = G(R⟦t⟧)`, contravariant in `H`. -/
@[expose] noncomputable def positiveLoopGroupFunctor :
    (_root_.CommHopfAlgCat.{v} k)ᵒᵖ ⥤ CommAlgCat.{w} k ⥤ GrpCat.{max v w} :=
  pointsFunctor ⋙ (Functor.whiskeringLeft _ _ _).obj (CommAlgCat.powerSeries k)

/-- The homomorphisms `L⁺G(R) → LG(R)`, natural in both `H` and `R`. -/
noncomputable def positiveLoopToLoop :
    positiveLoopGroupFunctor.{u, v, w} k ⟶ loopGroupFunctor k :=
  Functor.whiskerLeft pointsFunctor
    ((Functor.whiskeringLeft _ _ _).map (CommAlgCat.ofPowerSeries k))

/-- At a commutative Hopf algebra `H`, `loopGroupFunctor` is the loop group of `H`. -/
lemma loopGroupFunctor_obj (H : (_root_.CommHopfAlgCat.{v} k)ᵒᵖ) :
    (loopGroupFunctor.{u, v, w} k).obj H = HopfAlgebra.loopGroup k H.unop :=
  (rfl)

/-- At a commutative Hopf algebra `H`, `positiveLoopGroupFunctor` is the positive loop group of
`H`. -/
lemma positiveLoopGroupFunctor_obj (H : (_root_.CommHopfAlgCat.{v} k)ᵒᵖ) :
    (positiveLoopGroupFunctor.{u, v, w} k).obj H = HopfAlgebra.positiveLoopGroup k H.unop :=
  (rfl)

/-- A morphism of commutative Hopf algebras acts on loops by pre-composition. -/
lemma loopGroupFunctor_map_app_apply {H K : (_root_.CommHopfAlgCat.{v} k)ᵒᵖ} (φ : H ⟶ K)
    (R : CommAlgCat.{w} k) (g : (HopfAlgebra.loopGroup k H.unop).obj R) :
    ((loopGroupFunctor k).map φ).app R g = BialgHom.mapDomain φ.unop.hom g :=
  (rfl)

/-- A morphism of commutative Hopf algebras acts on positive loops by pre-composition. -/
lemma positiveLoopGroupFunctor_map_app_apply {H K : (_root_.CommHopfAlgCat.{v} k)ᵒᵖ}
    (φ : H ⟶ K) (R : CommAlgCat.{w} k) (g : (HopfAlgebra.positiveLoopGroup k H.unop).obj R) :
    ((positiveLoopGroupFunctor k).map φ).app R g = BialgHom.mapDomain φ.unop.hom g :=
  (rfl)

/-- At a commutative Hopf algebra `H`, `positiveLoopToLoop` is
`HopfAlgebra.positiveLoopToLoop`. -/
lemma positiveLoopToLoop_app (H : (_root_.CommHopfAlgCat.{v} k)ᵒᵖ) :
    (positiveLoopToLoop.{u, v, w} k).app H = HopfAlgebra.positiveLoopToLoop k H.unop :=
  (rfl)

end CommHopfAlgCat

end TauCeti
