/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.FixedPoints
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality

/-!
# Functoriality of scheme-valued points in the coefficient ring and fixed-locus descent

Let `X` be a scheme over `Spec k`. A `k`-algebra homomorphism `ψ : R →ₐ[k] S` induces a covariant
map `mapCodomain f ψ : Points (R := R) f → Points (R := S) f` by precomposing the scheme morphism
`Spec R ⟶ X` with `Spec ψ : Spec S ⟶ Spec R`. On every affine chart it agrees with post-composition
`x ↦ ψ.comp x` of coordinate algebra maps (`mapCodomain_chartPoint`).

Because the chart topology is coinduced by affine open immersions and `continuous_chartPoint` needs
no locality or unit hypotheses on the target ring, `mapCodomain f ψ` is continuous whenever `ψ` is
continuous (`continuous_mapCodomain`). When `S` is a local ring and `ψ` is a local homomorphism,
`R` is itself a local ring (`RingHom.domain_isLocalRing`) and `Spec ψ` preserves the closed point;
any `S`-point in the image of `mapCodomain f ψ` that lands in an affine open chart therefore comes
from an `R`-point in the same chart. This gives injectivity when `ψ` is injective
(`mapCodomain_injective`) and closed embeddings when `ψ` is a closed embedding
(`isClosedEmbedding_mapCodomain`), with no open-units, separation, or finiteness hypotheses on `R`,
`S`, or `X`.

When `S` is a local ring and `ψ : R →ₐ[k] S` is an injective map whose image is the fixed locus of
an endomorphism `σ : S →ₐ[k] S`, every `σ`-fixed `S`-point of `X` lands in a single affine open
chart, where `chartPoint_injective` reduces the fixed-point equation to the affine case. Thus
`Set.range (mapCodomain f ψ) = {y | mapCodomain f σ y = y}` (`range_mapCodomain_eq_fixedPoints`),
identifying `Points (R := R) f` homeomorphically with the `σ`-fixed locus of `Points (R := S) f`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and Prop. 3.1, pp. 2–4.
* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3, p. 12.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

section Algebraic

variable {k R S T : Type u} [CommRing k]
  [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
  {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}

/-- Covariant functoriality of scheme-valued points in the coefficient ring: a `k`-algebra map
`ψ : R →ₐ[k] S` sends an `R`-point `Spec R ⟶ X` to `Spec S ⟶ Spec R ⟶ X`. -/
noncomputable def mapCodomain (f : X ⟶ Spec (.of k)) (ψ : R →ₐ[k] S)
    (x : Points (R := R) f) : Points (R := S) f :=
  ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ x.val, by
    rw [Category.assoc, x.property, ← Spec.map_comp]
    congr 1
    ext c
    exact ψ.commutes c⟩

/-- The underlying scheme morphism of `mapCodomain f ψ x` is `Spec ψ ≫ x.val`. -/
@[simp]
theorem mapCodomain_val (f : X ⟶ Spec (.of k)) (ψ : R →ₐ[k] S) (x : Points (R := R) f) :
    (mapCodomain f ψ x).val = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ x.val :=
  (rfl)

/-- The identity coefficient map induces the identity on scheme-valued points. -/
@[simp]
theorem mapCodomain_id (f : X ⟶ Spec (.of k)) (x : Points (R := R) f) :
    mapCodomain f (AlgHom.id k R) x = x := by
  apply Subtype.ext
  simp [AlgHom.toRingHom_eq_coe]

/-- Composition of coefficient maps acts covariantly on scheme-valued points. -/
@[simp]
theorem mapCodomain_mapCodomain (f : X ⟶ Spec (.of k)) (ψ' : S →ₐ[k] T) (ψ : R →ₐ[k] S)
    (x : Points (R := R) f) :
    mapCodomain f ψ' (mapCodomain f ψ x) = mapCodomain f (ψ'.comp ψ) x := by
  apply Subtype.ext
  simp only [mapCodomain_val, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Change of coefficients commutes with morphisms of schemes over the base. -/
@[simp]
theorem map_mapCodomain (g : X ⟶ Y) (hg : g ≫ fY = f) (ψ : R →ₐ[k] S)
    (x : Points (R := R) f) :
    map g hg (mapCodomain f ψ x) = mapCodomain fY ψ (map g hg x) := by
  apply Subtype.ext
  simp

/-- On an affine chart, `mapCodomain` post-composes the coordinate algebra homomorphism with `ψ`. -/
@[simp]
theorem mapCodomain_chartPoint (f : X ⟶ Spec (.of k)) (ψ : R →ₐ[k] S)
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X) (hi : i ≫ f = Spec.algebraMap k A)
    (x : A →ₐ[k] R) :
    mapCodomain f ψ (chartPoint f A i hi x) = chartPoint f A i hi (ψ.comp x) := by
  apply Subtype.ext
  simp only [mapCodomain_val, chartPoint_val, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Under `Spec.homEquivAlgHom.symm`, `mapCodomain` corresponds to post-composition
`x ↦ ψ.comp x`. -/
@[simp]
theorem mapCodomain_homEquivAlgHom_symm
    (A : Type u) [CommRing A] [Algebra k A] (ψ : R →ₐ[k] S) (x : A →ₐ[k] R) :
    mapCodomain (Spec.algebraMap k A) ψ (Spec.homEquivAlgHom.symm x) =
      Spec.homEquivAlgHom.symm (ψ.comp x) := by
  apply Subtype.ext
  simp only [mapCodomain_val, Spec.homEquivAlgHom_symm_apply_val,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]

/-- Under `affineHomeomorph`, `mapCodomain` corresponds to post-composition `x ↦ ψ.comp x`. -/
theorem mapCodomain_affineHomeomorph [TopologicalSpace R] [TopologicalSpace S]
    (A : Type u) [CommRing A] [Algebra k A] (ψ : R →ₐ[k] S) (x : A →ₐ[k] R) :
    mapCodomain (Spec.algebraMap k A) ψ (affineHomeomorph (k := k) (R := R) A x) =
      affineHomeomorph (k := k) (R := S) A (ψ.comp x) := by
  simp

end Algebraic

section Topology

variable {k R S : Type u} [CommRing k]
  [CommRing R] [Algebra k R] [TopologicalSpace R]
  [CommRing S] [Algebra k S] [TopologicalSpace S]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Continuous change of coefficients is continuous on scheme-valued points, with no locality or
open-units assumption on `R` or `S`. -/
@[continuity, fun_prop]
theorem continuous_mapCodomain {ψ : R →ₐ[k] S} (hψ : Continuous ψ) :
    Continuous (mapCodomain f ψ) := by
  refine (continuous_iff f _).2 fun A i hi _ ↦ ?_
  have hcomp : mapCodomain f ψ ∘ chartPoint (R := R) f A i hi =
      chartPoint (R := S) f A i hi ∘ fun x ↦ ψ.comp x :=
    funext (mapCodomain_chartPoint f ψ A i hi)
  rw [hcomp]
  exact (continuous_chartPoint (R := S) f A i hi).comp (PointTopology.continuous_map_codomain ψ hψ)

/-- A bicontinuous `k`-algebra equivalence `e : R ≃ₐ[k] S` induces a homeomorphism on scheme-valued
points. -/
noncomputable def algEquivHomeomorph {e : R ≃ₐ[k] S} (he : Continuous e)
    (hes : Continuous e.symm) :
    Points (R := R) f ≃ₜ Points (R := S) f where
  toFun := mapCodomain f (e : R →ₐ[k] S)
  invFun := mapCodomain f (e.symm : S →ₐ[k] R)
  left_inv x := by rw [mapCodomain_mapCodomain, e.symm_comp, mapCodomain_id]
  right_inv y := by rw [mapCodomain_mapCodomain, e.comp_symm, mapCodomain_id]
  continuous_toFun := continuous_mapCodomain f he
  continuous_invFun := continuous_mapCodomain f hes

/-- `algEquivHomeomorph` acts as `mapCodomain f e`. -/
@[simp]
theorem algEquivHomeomorph_apply {e : R ≃ₐ[k] S} (he : Continuous e) (hes : Continuous e.symm)
    (x : Points (R := R) f) :
    algEquivHomeomorph f he hes x = mapCodomain f (e : R →ₐ[k] S) x := (rfl)

/-- The inverse of `algEquivHomeomorph` is `algEquivHomeomorph` for `e.symm`. -/
@[simp]
theorem algEquivHomeomorph_symm {e : R ≃ₐ[k] S} (he : Continuous e) (hes : Continuous e.symm) :
    (algEquivHomeomorph f he hes).symm = algEquivHomeomorph f hes he := (rfl)

end Topology

section LocalRing

variable {k R S : Type u} [CommRing k]
  [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Along a local homomorphism `ψ : R →ₐ[k] S` of local rings, `mapCodomain f ψ x` sends the closed
point of `Spec S` to the same point of `X` as `x` sends the closed point of `Spec R`. -/
theorem mapCodomain_closedPoint [IsLocalRing R] [IsLocalRing S] (ψ : R →ₐ[k] S) [IsLocalHom ψ]
    (x : Points (R := R) f) :
    (mapCodomain f ψ x).val (IsLocalRing.closedPoint S) = x.val (IsLocalRing.closedPoint R) := by
  have : IsLocalHom (CommRingCat.ofHom ψ.toRingHom).hom :=
    ⟨IsLocalHom.map_nonunit (f := ψ)⟩
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom ψ.toRingHom)) x.val
    (IsLocalRing.closedPoint S)).trans
    (congrArg x.val (Spec_closedPoint (R := .of R) (S := .of S)
      (f := CommRingCat.ofHom ψ.toRingHom)))

/-- An injective local homomorphism into a local coefficient ring `S` is injective on
scheme-valued points (`IsLocalRing R` follows via `RingHom.domain_isLocalRing`). -/
theorem mapCodomain_injective [IsLocalRing S] {ψ : R →ₐ[k] S} [IsLocalHom ψ]
    (hψ : Function.Injective ψ) :
    Function.Injective (mapCodomain f ψ) := by
  have : IsLocalHom ψ.toRingHom := ⟨IsLocalHom.map_nonunit (f := ψ)⟩
  have : IsLocalRing R := ψ.toRingHom.domain_isLocalRing
  intro x y hxy
  obtain ⟨A, i, hi, _, a, rfl⟩ := exists_mem_range_chartPoint f x
  have hy_mem : y ∈ Set.range (chartPoint f A i hi) := by
    rw [mem_range_chartPoint_iff_closedPoint, ← mapCodomain_closedPoint f ψ y, ← hxy,
      mapCodomain_closedPoint, ← mem_range_chartPoint_iff_closedPoint f A i hi]
    exact ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ := hy_mem
  rw [mapCodomain_chartPoint, mapCodomain_chartPoint] at hxy
  have hab : ψ.comp a = ψ.comp b := chartPoint_injective f A i hi hxy
  exact congrArg (chartPoint f A i hi) (AlgHom.ext fun c ↦ hψ (DFunLike.congr_fun hab c))

/-- Pulling back the `mapCodomain` image of a set along an affine open chart commutes with
post-composition by `ψ`, because `Spec ψ` preserves the closed point. -/
private theorem preimage_chartPoint_image_mapCodomain [IsLocalRing S]
    (ψ : R →ₐ[k] S) [IsLocalHom ψ] (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] (t : Set (Points (R := R) f)) :
    chartPoint (R := S) f A i hi ⁻¹' (mapCodomain f ψ '' t) =
      (fun x : A →ₐ[k] R ↦ ψ.comp x) '' (chartPoint (R := R) f A i hi ⁻¹' t) := by
  have : IsLocalHom ψ.toRingHom := ⟨IsLocalHom.map_nonunit (f := ψ)⟩
  have : IsLocalRing R := ψ.toRingHom.domain_isLocalRing
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, hyz⟩
    have hy_chart : y ∈ Set.range (chartPoint f A i hi) := by
      rw [mem_range_chartPoint_iff_closedPoint, ← mapCodomain_closedPoint f ψ y, hyz,
        ← mem_range_chartPoint_iff_closedPoint f A i hi]
      exact ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hy_chart
    rw [mapCodomain_chartPoint] at hyz
    exact ⟨x, hy, chartPoint_injective f A i hi hyz⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨chartPoint f A i hi x, hx, mapCodomain_chartPoint f ψ A i hi x⟩

/-- A local closed embedding into a local coefficient ring `S` induces a closed embedding on
scheme-valued points, with no open-units, separation, or finiteness hypotheses. -/
theorem isClosedEmbedding_mapCodomain [TopologicalSpace R] [TopologicalSpace S]
    [IsLocalRing S] {ψ : R →ₐ[k] S} [IsLocalHom ψ] (hψ : IsClosedEmbedding ψ) :
    IsClosedEmbedding (mapCodomain f ψ) := by
  refine .of_continuous_injective_isClosedMap (continuous_mapCodomain f hψ.continuous)
    (mapCodomain_injective f hψ.injective) fun t ht ↦ ?_
  rw [← isOpen_compl_iff, isOpen_iff]
  intro A i hi _
  suffices IsClosed (chartPoint (R := S) f A i hi ⁻¹' (mapCodomain f ψ '' t)) by
    simpa only [Set.preimage_compl] using this.isOpen_compl
  rw [preimage_chartPoint_image_mapCodomain f ψ A i hi t]
  exact (PointTopology.isClosedEmbedding_map_codomain ψ hψ).isClosedMap _
    (ht.preimage (continuous_chartPoint (R := R) f A i hi))

/-- Over a local coefficient ring `S`, if `ψ : R →ₐ[k] S` is injective with image equal to the
fixed locus of `σ : S →ₐ[k] S`, then the `S`-points of `X` fixed by `mapCodomain f σ` are precisely
the images of `R`-points. Neither `IsLocalRing R` nor `IsLocalHom ψ` is required. -/
theorem range_mapCodomain_eq_fixedPoints [IsLocalRing S] {ψ : R →ₐ[k] S}
    (hψ : Function.Injective ψ) (σ : S →ₐ[k] S) (hfix : {s : S | σ s = s} = Set.range ψ) :
    Set.range (mapCodomain f ψ) = {y : Points (R := S) f | mapCodomain f σ y = y} := by
  have hcomp : σ.comp ψ = ψ := AlgHom.ext fun r ↦ by
    have hr : ψ r ∈ {s : S | σ s = s} := hfix ▸ ⟨r, rfl⟩
    exact hr
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    simp [mapCodomain_mapCodomain, hcomp]
  · obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint f y
    rw [Set.mem_ofPred_eq, mapCodomain_chartPoint] at hy
    have hz : σ.comp z = z := chartPoint_injective f A i hi hy
    have hz_mem : z ∈ Set.range (fun x : A →ₐ[k] R ↦ ψ.comp x) := by
      rw [PointTopology.range_comp_eq_fixedPoints hψ σ hfix]
      exact hz
    obtain ⟨x, rfl⟩ := hz_mem
    exact ⟨chartPoint f A i hi x, mapCodomain_chartPoint f ψ A i hi x⟩

/-- When `ψ : R →ₐ[k] S` is a local closed embedding into a local ring `S` whose image is the fixed
locus of `σ : S →ₐ[k] S`, `mapCodomain f ψ` identifies the `R`-points of `X` homeomorphically with
the `σ`-fixed subspace of `S`-points. -/
noncomputable def fixedPointsHomeomorphOfIsClosedEmbedding [TopologicalSpace R]
    [TopologicalSpace S] [IsLocalRing S] {ψ : R →ₐ[k] S} [IsLocalHom ψ]
    (hψ : IsClosedEmbedding ψ) {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ) :
    Points (R := R) f ≃ₜ {y : Points (R := S) f // mapCodomain f σ y = y} :=
  (isClosedEmbedding_mapCodomain f hψ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_mapCodomain_eq_fixedPoints f hψ.injective σ hfix))

/-- Coercing `fixedPointsHomeomorphOfIsClosedEmbedding` to an `S`-point yields
`mapCodomain f ψ x`. -/
@[simp]
theorem coe_fixedPointsHomeomorphOfIsClosedEmbedding_apply [TopologicalSpace R]
    [TopologicalSpace S] [IsLocalRing S] {ψ : R →ₐ[k] S} [IsLocalHom ψ]
    (hψ : IsClosedEmbedding ψ) {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ)
    (x : Points (R := R) f) :
    (fixedPointsHomeomorphOfIsClosedEmbedding f hψ hfix x : Points (R := S) f) =
      mapCodomain f ψ x := (rfl)

/-- Applying `mapCodomain f ψ` to the inverse of `fixedPointsHomeomorphOfIsClosedEmbedding`
recovers the `σ`-fixed scheme-valued point. -/
@[simp]
theorem mapCodomain_fixedPointsHomeomorphOfIsClosedEmbedding_symm [TopologicalSpace R]
    [TopologicalSpace S] [IsLocalRing S] {ψ : R →ₐ[k] S} [IsLocalHom ψ]
    (hψ : IsClosedEmbedding ψ) {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ)
    (y : {y : Points (R := S) f // mapCodomain f σ y = y}) :
    mapCodomain f ψ ((fixedPointsHomeomorphOfIsClosedEmbedding f hψ hfix).symm y) = y.1 := by
  rw [← coe_fixedPointsHomeomorphOfIsClosedEmbedding_apply f hψ hfix, Homeomorph.apply_symm_apply]

end LocalRing

end TauCeti.SchemePointTopology
