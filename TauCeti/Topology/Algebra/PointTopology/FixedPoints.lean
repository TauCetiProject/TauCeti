/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
public import TauCeti.Topology.Algebra.PointTopology.IntegralPoints
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Fixed loci of coefficient actions on spaces and groups of points

Let `ψ : R →ₐ[k] S` be an injective homomorphism of `k`-algebras whose image is the common fixed
locus in `S` of an endomorphism `σ : S →ₐ[k] S` (or of an arbitrary family `σ : ι → (S →ₐ[k] S)`).
For every `k`-algebra `A`, post-composition with `σ` acts on the `S`-points `A →ₐ[k] S`, and a
point is fixed by `σ` if and only if each of its values lies in `Set.range ψ`, hence if and only if
it comes from a unique `R`-point `A →ₐ[k] R`.

When `R` and `S` carry topologies for which `ψ` is a topological embedding, this identifies
`A →ₐ[k] R` homeomorphically with the fixed subspace `{x : A →ₐ[k] S // σ.comp x = x}` for the
point topologies (`TauCeti.PointTopology.fixedPointsHomeomorph`). For a Hopf algebra `H` over `k`
and commutative coefficient algebras `R` and `S`, post-composition is the group homomorphism
`AlgHom.mapValue`, so `WithConv (H →ₐ[k] R)` is isomorphic as a topological group to the fixed
subgroup `(AlgHom.mapValue σ).eqLocus (MonoidHom.id _)` of `WithConv (H →ₐ[k] S)`
(`TauCeti.PointTopology.fixedPointsContinuousMulEquiv`).

In a compatible extension `K → L` of valued fields whose base image is cut out by `σ : L →ₐ[K] L`,
integrality `v ≤ 1` is reflected by `ValuativeExtension K L`: an `𝒪[K]`-algebra map `A →ₐ[𝒪[K]] L`
(or convolution point of an `𝒪[K]`-Hopf algebra) whose values lie in `𝒪[L]` and are fixed by `σ`
comes from a unique integral point over `𝒪[K]`.

## Main declarations

* `AlgEquiv.pointsHomeomorph` and `AlgEquiv.mapValueContinuousMulEquiv`: homeomorphism on spaces of
  points and topological-group isomorphism on convolution groups induced by a bicontinuous algebra
  equivalence of coefficient rings.
* `TauCeti.PointTopology.range_comp_eq_iInter_fixedPoints`,
  `TauCeti.PointTopology.range_comp_eq_fixedPoints`, and
  `TauCeti.PointTopology.fixedPointsHomeomorph`: descent of affine points to `R` along an
  injective or embedding map `ψ : R →ₐ[k] S` onto a fixed locus, and closedness of the fixed locus
  over Hausdorff coefficients (`TauCeti.PointTopology.isClosed_fixedPoints_comp`).
* `TauCeti.PointTopology.mrange_mapValue_eq_eqLocusM`,
  `TauCeti.PointTopology.range_mapValue_eq_eqLocus`, and
  `TauCeti.PointTopology.fixedPointsContinuousMulEquiv`: descent of convolution monoids and
  topological groups of points to the fixed submonoid or subgroup.
* `TauCeti.PointTopology.range_integralPoints_eq_fixedPoints` and
  `TauCeti.PointTopology.range_mapValue_integer_eq_fixedPoints`: integral points over `𝒪[K]` as the
  `σ`-fixed integral-valued `L`-points in a compatible valued field extension `K → L`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3, p. 12.
-/

public section

open Topology WithConv ValuativeRel
open scoped TauCeti.PointTopology

namespace AlgEquiv

section Semiring

variable {k R S : Type*} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S] [Algebra k S]
  [TopologicalSpace R] [TopologicalSpace S]

/-- A bicontinuous `k`-algebra equivalence `e : R ≃ₐ[k] S` of coefficient rings induces a
homeomorphism `(A →ₐ[k] R) ≃ₜ (A →ₐ[k] S)` on spaces of points by post-composition. -/
noncomputable def pointsHomeomorph (e : R ≃ₐ[k] S) (A : Type*) [Semiring A] [Algebra k A]
    (he : Continuous e) (hes : Continuous e.symm) :
    (A →ₐ[k] R) ≃ₜ (A →ₐ[k] S) where
  toFun x := (e : R →ₐ[k] S).comp x
  invFun y := (e.symm : S →ₐ[k] R).comp y
  left_inv x := AlgHom.ext fun a ↦ e.symm_apply_apply (x a)
  right_inv y := AlgHom.ext fun a ↦ e.apply_symm_apply (y a)
  continuous_toFun := TauCeti.PointTopology.continuous_map_codomain (e : R →ₐ[k] S) he
  continuous_invFun := TauCeti.PointTopology.continuous_map_codomain (e.symm : S →ₐ[k] R) hes

/-- `pointsHomeomorph` acts by post-composing a point with `e`. -/
@[simp]
theorem pointsHomeomorph_apply (e : R ≃ₐ[k] S) {A : Type*} [Semiring A] [Algebra k A]
    (he : Continuous e) (hes : Continuous e.symm) (x : A →ₐ[k] R) :
    e.pointsHomeomorph A he hes x = (e : R →ₐ[k] S).comp x := (rfl)

/-- The inverse of `pointsHomeomorph` is `pointsHomeomorph` for `e.symm`. -/
@[simp]
theorem pointsHomeomorph_symm (e : R ≃ₐ[k] S) {A : Type*} [Semiring A] [Algebra k A]
    (he : Continuous e) (hes : Continuous e.symm) :
    (e.pointsHomeomorph A he hes).symm = e.symm.pointsHomeomorph A hes he := (rfl)

end Semiring

section Bialgebra

variable {k R S : Type*} [CommSemiring k]
  [CommSemiring R] [Algebra k R] [TopologicalSpace R]
  [CommSemiring S] [Algebra k S] [TopologicalSpace S]

/-- A bicontinuous `k`-algebra equivalence `e : R ≃ₐ[k] S` of commutative coefficient rings induces
a topological multiplicative isomorphism on the convolution monoids of points of a bialgebra. -/
noncomputable def mapValueContinuousMulEquiv (e : R ≃ₐ[k] S) (H : Type*) [Semiring H]
    [Bialgebra k H] (he : Continuous e) (hes : Continuous e.symm) :
    WithConv (H →ₐ[k] R) ≃ₜ* WithConv (H →ₐ[k] S) where
  toMulEquiv := e.mapValueMulEquiv
  continuous_toFun := by
    have heq : (e.mapValueMulEquiv (H := H)).toFun = AlgHom.mapValue (e : R →ₐ[k] S) :=
      funext e.mapValueMulEquiv_apply
    rw [heq]
    exact AlgHom.continuous_mapValue he
  continuous_invFun := by
    have heq : (e.mapValueMulEquiv (H := H)).invFun = AlgHom.mapValue (e.symm : S →ₐ[k] R) := by
      ext g
      rw [MulEquiv.invFun_eq_symm, mapValueMulEquiv_symm, mapValueMulEquiv_apply]
    rw [heq]
    exact AlgHom.continuous_mapValue hes

/-- `mapValueContinuousMulEquiv` acts as `AlgHom.mapValue e`. -/
@[simp]
theorem mapValueContinuousMulEquiv_apply (e : R ≃ₐ[k] S) {H : Type*} [Semiring H]
    [Bialgebra k H] (he : Continuous e) (hes : Continuous e.symm) (f : WithConv (H →ₐ[k] R)) :
    e.mapValueContinuousMulEquiv H he hes f = AlgHom.mapValue (e : R →ₐ[k] S) f :=
  e.mapValueMulEquiv_apply f

/-- The inverse of `mapValueContinuousMulEquiv` is `mapValueContinuousMulEquiv` for `e.symm`. -/
@[simp]
theorem mapValueContinuousMulEquiv_symm (e : R ≃ₐ[k] S) {H : Type*} [Semiring H]
    [Bialgebra k H] (he : Continuous e) (hes : Continuous e.symm) :
    (e.mapValueContinuousMulEquiv H he hes).symm =
      e.symm.mapValueContinuousMulEquiv H hes he :=
  ContinuousMulEquiv.ext fun g ↦ (e.mapValueContinuousMulEquiv H he hes).symm_apply_eq.2 <|
    ((DFunLike.congr_fun (by
      rw [← AlgHom.mapValue_comp, e.comp_symm, AlgHom.mapValue_id] :
        (AlgHom.mapValue (H := H) (e : R →ₐ[k] S)).comp
          (AlgHom.mapValue (e.symm : S →ₐ[k] R)) = MonoidHom.id _) g).symm.trans
      (congrArg (AlgHom.mapValue (H := H) (e : R →ₐ[k] S))
        (e.symm.mapValueContinuousMulEquiv_apply hes he g)).symm).trans
      (e.mapValueContinuousMulEquiv_apply he hes _).symm

/-- Forgetting the topology on `mapValueContinuousMulEquiv` recovers `mapValueMulEquiv`. -/
theorem toMulEquiv_mapValueContinuousMulEquiv (e : R ≃ₐ[k] S) {H : Type*} [Semiring H]
    [Bialgebra k H] (he : Continuous e) (hes : Continuous e.symm) :
    (e.mapValueContinuousMulEquiv H he hes).toMulEquiv = e.mapValueMulEquiv := (rfl)

end Bialgebra

end AlgEquiv

namespace TauCeti.PointTopology

section Affine

variable {k A R S : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [Semiring R] [Algebra k R] [Semiring S] [Algebra k S]

/-- For an injective coefficient homomorphism `ψ : R →ₐ[k] S` whose image is the common fixed locus
of a family `σ : ι → (S →ₐ[k] S)`, the `S`-points of `A` fixed under post-composition with every
`σ i` are precisely the images of `R`-points. -/
theorem range_comp_eq_iInter_fixedPoints {ι : Sort*} {ψ : R →ₐ[k] S}
    (hψ : Function.Injective ψ) (σ : ι → (S →ₐ[k] S))
    (hfix : {s : S | ∀ i, σ i s = s} = Set.range ψ) :
    Set.range (fun x : A →ₐ[k] R ↦ ψ.comp x) = {x : A →ₐ[k] S | ∀ i, (σ i).comp x = x} := by
  rw [AlgHom.range_comp_left_of_injective ψ hψ, ← hfix]
  ext x
  simp only [Set.mem_ofPred_eq, AlgHom.ext_iff, AlgHom.comp_apply]
  exact forall_comm

/-- For an injective coefficient homomorphism `ψ : R →ₐ[k] S` whose image is the fixed locus of an
endomorphism `σ : S →ₐ[k] S`, the `S`-points of `A` fixed by `σ` are precisely the images of
`R`-points. -/
theorem range_comp_eq_fixedPoints {ψ : R →ₐ[k] S} (hψ : Function.Injective ψ) (σ : S →ₐ[k] S)
    (hfix : {s : S | σ s = s} = Set.range ψ) :
    Set.range (fun x : A →ₐ[k] R ↦ ψ.comp x) = {x : A →ₐ[k] S | σ.comp x = x} := by
  simpa using range_comp_eq_iInter_fixedPoints (A := A) hψ (fun _ : Unit ↦ σ) (by simpa using hfix)

/-- Over a Hausdorff coefficient semiring `S`, the fixed locus of a continuous algebra endomorphism
`σ : S →ₐ[k] S` on `A →ₐ[k] S` is closed in the point topology. -/
theorem isClosed_fixedPoints_comp [TopologicalSpace S] [T2Space S] {σ : S →ₐ[k] S}
    (hσ : Continuous σ) :
    IsClosed {x : A →ₐ[k] S | σ.comp x = x} :=
  isClosed_eq (continuous_map_codomain σ hσ) continuous_id

/-- When `ψ : R →ₐ[k] S` is a topological embedding whose image is the fixed locus of
`σ : S →ₐ[k] S`, post-composition with `ψ` is a homeomorphism from the `R`-points of `A` onto the
subspace of `S`-points fixed by `σ`. -/
noncomputable def fixedPointsHomeomorph (A : Type*) [Semiring A] [Algebra k A]
    [TopologicalSpace R] [TopologicalSpace S] {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ)
    {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ) :
    (A →ₐ[k] R) ≃ₜ {x : A →ₐ[k] S // σ.comp x = x} :=
  (isEmbedding_map_codomain (A := A) ψ hψ).toHomeomorph.trans
    (Homeomorph.setCongr (range_comp_eq_fixedPoints hψ.injective σ hfix))

/-- Coercing `fixedPointsHomeomorph` to an `S`-point gives `ψ.comp x`. -/
@[simp]
theorem coe_fixedPointsHomeomorph_apply [TopologicalSpace R] [TopologicalSpace S]
    {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ) {σ : S →ₐ[k] S}
    (hfix : {s : S | σ s = s} = Set.range ψ) (x : A →ₐ[k] R) :
    (fixedPointsHomeomorph A hψ hfix x : A →ₐ[k] S) = ψ.comp x := (rfl)

/-- Post-composing the inverse of `fixedPointsHomeomorph` with `ψ` recovers the `σ`-fixed point. -/
@[simp]
theorem comp_fixedPointsHomeomorph_symm [TopologicalSpace R] [TopologicalSpace S]
    {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ) {σ : S →ₐ[k] S}
    (hfix : {s : S | σ s = s} = Set.range ψ) (y : {x : A →ₐ[k] S // σ.comp x = x}) :
    ψ.comp ((fixedPointsHomeomorph A hψ hfix).symm y) = y.1 := by
  rw [← coe_fixedPointsHomeomorph_apply hψ hfix, Homeomorph.apply_symm_apply]

end Affine

section Group

variable {k R S : Type*} [CommSemiring k]
  [CommSemiring R] [Algebra k R] [CommSemiring S] [Algebra k S]

/-- For a bialgebra `H` and an injective coefficient map `ψ : R →ₐ[k] S` whose image is the fixed
locus of `σ : S →ₐ[k] S`, the submonoid image of `AlgHom.mapValue ψ` is the equalizer submonoid of
`AlgHom.mapValue σ` and the identity. -/
theorem mrange_mapValue_eq_eqLocusM {H : Type*} [Semiring H] [Bialgebra k H]
    {ψ : R →ₐ[k] S} (hψ : Function.Injective ψ) (σ : S →ₐ[k] S)
    (hfix : {s : S | σ s = s} = Set.range ψ) :
    MonoidHom.mrange (AlgHom.mapValue (H := H) ψ) =
      (AlgHom.mapValue (H := H) σ).eqLocusM (MonoidHom.id _) := by
  ext f
  rw [AlgHom.mem_mrange_mapValue_iff hψ, MonoidHom.mem_eqLocusM, MonoidHom.id_apply,
    AlgHom.mapValue_apply, ← WithConv.ofConv_injective.eq_iff, ofConv_toConv, AlgHom.ext_iff]
  refine forall_congr' fun h ↦ ?_
  rw [AlgHom.mem_range, ← Set.mem_range, ← hfix, Set.mem_ofPred_eq, AlgHom.comp_apply]

/-- For a Hopf algebra `H` and an injective coefficient map `ψ : R →ₐ[k] S` whose image is the
fixed locus of `σ : S →ₐ[k] S`, the image subgroup of `AlgHom.mapValue ψ` in `WithConv (H →ₐ[k] S)`
is the `σ`-fixed subgroup `MonoidHom.eqLocus (AlgHom.mapValue σ) (MonoidHom.id _)`. -/
theorem range_mapValue_eq_eqLocus {H : Type*} [Semiring H] [HopfAlgebra k H]
    {ψ : R →ₐ[k] S} (hψ : Function.Injective ψ) (σ : S →ₐ[k] S)
    (hfix : {s : S | σ s = s} = Set.range ψ) :
    MonoidHom.range (G := WithConv (H →ₐ[k] R)) (N := WithConv (H →ₐ[k] S))
        (AlgHom.mapValue (H := H) ψ) =
      MonoidHom.eqLocus (G := WithConv (H →ₐ[k] S))
        (AlgHom.mapValue (H := H) σ) (MonoidHom.id _) := by
  ext f
  exact SetLike.ext_iff.1 (mrange_mapValue_eq_eqLocusM (H := H) hψ σ hfix) f

/-- Over a Hausdorff commutative coefficient semiring `S`, the `σ`-fixed locus of a continuous
endomorphism `σ : S →ₐ[k] S` on `WithConv (H →ₐ[k] S)` is closed. -/
theorem isClosed_eqLocus_mapValue {H : Type*} [Semiring H] [Bialgebra k H]
    [TopologicalSpace S] [T2Space S] {σ : S →ₐ[k] S} (hσ : Continuous σ) :
    IsClosed ((AlgHom.mapValue (H := H) σ).eqLocusM (MonoidHom.id _) :
      Set (WithConv (H →ₐ[k] S))) :=
  isClosed_eq (AlgHom.continuous_mapValue hσ) continuous_id

/-- When `ψ : R →ₐ[k] S` is a topological embedding whose image is the fixed locus of
`σ : S →ₐ[k] S`, `AlgHom.mapValue ψ` induces an isomorphism of topological groups from
`WithConv (H →ₐ[k] R)` onto the `σ`-fixed subgroup of `WithConv (H →ₐ[k] S)`. -/
noncomputable def fixedPointsContinuousMulEquiv (H : Type*) [Semiring H] [HopfAlgebra k H]
    [TopologicalSpace R] [TopologicalSpace S] {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ)
    {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ) :
    WithConv (H →ₐ[k] R) ≃ₜ*
      MonoidHom.eqLocus (G := WithConv (H →ₐ[k] S))
        (AlgHom.mapValue (H := H) σ) (MonoidHom.id _) := by
  have hrange := range_mapValue_eq_eqLocus (H := H) hψ.injective σ hfix
  let φ' : WithConv (H →ₐ[k] R) →*
      MonoidHom.eqLocus (G := WithConv (H →ₐ[k] S))
        (AlgHom.mapValue (H := H) σ) (MonoidHom.id _) :=
    (AlgHom.mapValue (H := H) ψ).codRestrict _ fun x ↦ hrange ▸ ⟨x, rfl⟩
  have hbij : Function.Bijective φ' :=
    ⟨fun x y h ↦ AlgHom.mapValue_injective hψ.injective (congrArg Subtype.val h),
      fun ⟨y, hy⟩ ↦ by
        obtain ⟨x, rfl⟩ := hrange.symm ▸ hy
        exact ⟨x, Subtype.ext rfl⟩⟩
  let emul := MulEquiv.ofBijective φ' hbij
  exact
    { toMulEquiv := emul
      continuous_toFun := continuous_induced_rng.2 (AlgHom.continuous_mapValue hψ.continuous)
      continuous_invFun := by
        refine (AlgHom.isEmbedding_mapValue (H₁ := H) hψ).isInducing.continuous_iff.2 ?_
        have hcomp : AlgHom.mapValue (H := H) ψ ∘ emul.invFun = Subtype.val :=
          funext fun y ↦ congrArg Subtype.val (emul.apply_symm_apply y)
        rw [hcomp]
        exact continuous_subtype_val }

/-- Coercing `fixedPointsContinuousMulEquiv` to `WithConv (H →ₐ[k] S)` gives
`AlgHom.mapValue ψ f`. -/
@[simp]
theorem coe_fixedPointsContinuousMulEquiv_apply {H : Type*} [Semiring H] [HopfAlgebra k H]
    [TopologicalSpace R] [TopologicalSpace S] {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ)
    {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ) (f : WithConv (H →ₐ[k] R)) :
    (fixedPointsContinuousMulEquiv H hψ hfix f : WithConv (H →ₐ[k] S)) =
      AlgHom.mapValue ψ f := (rfl)

/-- Applying `AlgHom.mapValue ψ` to the inverse of `fixedPointsContinuousMulEquiv` recovers the
`σ`-fixed point. -/
theorem mapValue_fixedPointsContinuousMulEquiv_symm {H : Type*} [Semiring H] [HopfAlgebra k H]
    [TopologicalSpace R] [TopologicalSpace S] {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ)
    {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ)
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[k] S))
      (AlgHom.mapValue (H := H) σ) (MonoidHom.id _)) :
    AlgHom.mapValue ψ ((fixedPointsContinuousMulEquiv H hψ hfix).symm g) = g.1 :=
  congrArg Subtype.val ((fixedPointsContinuousMulEquiv H hψ hfix).apply_symm_apply g)

/-- Post-composing the underlying algebra map of `(fixedPointsContinuousMulEquiv H hψ hfix).symm g`
with `ψ` recovers `g.1.ofConv`. -/
@[simp]
theorem comp_ofConv_fixedPointsContinuousMulEquiv_symm {H : Type*} [Semiring H] [HopfAlgebra k H]
    [TopologicalSpace R] [TopologicalSpace S] {ψ : R →ₐ[k] S} (hψ : IsEmbedding ψ)
    {σ : S →ₐ[k] S} (hfix : {s : S | σ s = s} = Set.range ψ)
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[k] S))
      (AlgHom.mapValue (H := H) σ) (MonoidHom.id _)) :
    ψ.comp ((fixedPointsContinuousMulEquiv H hψ hfix).symm g).ofConv = g.1.ofConv := by
  simpa only [AlgHom.mapValue_apply, ← WithConv.ofConv_injective.eq_iff, ofConv_toConv] using
    mapValue_fixedPointsContinuousMulEquiv_symm hψ hfix g

end Group

section Integral

/-- In a compatible injective extension `K → L` of valued rings where `{z : L | σ z = z}` is the
image of `K`, an `𝒪[K]`-algebra map `A →ₐ[𝒪[K]] L` comes from an integral point `A →ₐ[𝒪[K]] 𝒪[K]`
if and only if all of its values lie in `𝒪[L]` and it is fixed by `σ`. -/
theorem range_integralPoints_eq_fixedPoints {K L A : Type*} [CommRing K] [ValuativeRel K]
    [Ring L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [Semiring A] [Algebra 𝒪[K] A]
    (hψ : Function.Injective (algebraMap K L)) (σ : L →ₐ[K] L)
    (hfix : {z : L | σ z = z} = Set.range (algebraMap K L)) :
    Set.range (fun x : A →ₐ[𝒪[K]] 𝒪[K] ↦ (Algebra.ofId 𝒪[K] L).comp x) =
      {x : A →ₐ[𝒪[K]] L | (∀ a, x a ∈ 𝒪[L]) ∧ (σ.restrictScalars 𝒪[K]).comp x = x} := by
  have hinj : Function.Injective (Algebra.ofId 𝒪[K] L) := hψ.comp injective_ofId_integer
  have hrange : Set.range (Algebra.ofId 𝒪[K] L) = {z : L | z ∈ 𝒪[L] ∧ σ z = z} := by
    ext z
    refine ⟨?_, fun ⟨hzO, hzσ⟩ ↦ ?_⟩
    · rintro ⟨x, rfl⟩
      have hmap : Algebra.ofId 𝒪[K] L x = algebraMap K L (x : K) :=
        IsScalarTower.algebraMap_apply 𝒪[K] K L x
      rw [hmap]
      exact ⟨(Valuation.HasExtension.val_algebraMap (vA := valuation L) x) ▸
        (algebraMap 𝒪[K] 𝒪[L] x).2, σ.commutes (x : K)⟩
    · have hmem : z ∈ Set.range (algebraMap K L) := hfix ▸ hzσ
      obtain ⟨r, rfl⟩ := hmem
      have hr : r ∈ 𝒪[K] := by
        rw [Valuation.mem_integer_iff,
          ← ValuativeExtension.valuation_algebraMap_le_one_iff (A := K) (B := L)]
        exact hzO
      exact ⟨⟨r, hr⟩, (IsScalarTower.algebraMap_apply 𝒪[K] K L ⟨r, hr⟩).symm⟩
  rw [AlgHom.range_comp_left_of_injective _ hinj, hrange]
  ext x
  simp [forall_and, AlgHom.ext_iff]

/-- For an `𝒪[K]`-Hopf algebra `H` and a compatible injective extension `K → L` of commutative
valued rings whose base image is cut out by `σ : L →ₐ[K] L`, the image of the integral points
`WithConv (H →ₐ[𝒪[K]] 𝒪[K])` in `WithConv (H →ₐ[𝒪[K]] L)` consists of the `σ`-fixed points with
values in `𝒪[L]`. -/
theorem range_mapValue_integer_eq_fixedPoints {K L H : Type*} [CommRing K] [ValuativeRel K]
    [CommRing L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [Semiring H]
    [HopfAlgebra 𝒪[K] H] (hψ : Function.Injective (algebraMap K L)) (σ : L →ₐ[K] L)
    (hfix : {z : L | σ z = z} = Set.range (algebraMap K L)) :
    ((MonoidHom.range (G := WithConv (H →ₐ[𝒪[K]] 𝒪[K])) (N := WithConv (H →ₐ[𝒪[K]] L))
      (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[K] L)) : Subgroup _) :
      Set (WithConv (H →ₐ[𝒪[K]] L))) =
      {f : WithConv (H →ₐ[𝒪[K]] L) |
        (∀ h, f.ofConv h ∈ 𝒪[L]) ∧ AlgHom.mapValue (σ.restrictScalars 𝒪[K]) f = f} := by
  ext f
  have hmem : f ∈ MonoidHom.range (G := WithConv (H →ₐ[𝒪[K]] 𝒪[K])) (N := WithConv (H →ₐ[𝒪[K]] L))
        (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[K] L)) ↔
      f.ofConv ∈ Set.range (fun x : H →ₐ[𝒪[K]] 𝒪[K] ↦ (Algebra.ofId 𝒪[K] L).comp x) := by
    refine ⟨fun ⟨g, hg⟩ ↦ ⟨g.ofConv, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨toConv x, ?_⟩⟩
    · rw [← hg, AlgHom.mapValue_apply, ofConv_toConv]
    · apply WithConv.ofConv_injective
      rw [AlgHom.mapValue_apply, ofConv_toConv]
      exact hx
  rw [SetLike.mem_coe, hmem, range_integralPoints_eq_fixedPoints hψ σ hfix, Set.mem_ofPred_eq,
    Set.mem_ofPred_eq, ← WithConv.ofConv_injective.eq_iff, AlgHom.mapValue_apply, ofConv_toConv]

end Integral

end TauCeti.PointTopology
