/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Integral models of affine groups and their local and global integral points

An `S`-integral model `IntegralModel R K H S` of `G = Spec H` packages a finitely presented
commutative Hopf algebra `coordinate` over `S.integer K` with
`baseChangeEquiv : K ⊗[S.integer K] coordinate ≃ₐc[K] H`. Via `pointsContinuousMulEquiv`,
`subalgebraPointsHom`, and `subalgebraPoints`, a model `M` defines:
* constructors `ofFiniteType`, `ofBaseRing`, and `trivial` with their generic-fibre
  identifications and point characterizations;
* open closed (compact for finite residue fields) subgroups `M.localPoints v hv ≤ G(K_v)` for
  `v ∉ S`, and `M.level v`;
* `T`-integral subgroups `M.globalPoints T hST ≤ G(K)`, scalar enlargement `M.enlarge hSS'`, and
  eventual model independence `level_eventuallyEq`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3 and Thm. 3.4.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open Filter IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped TensorProduct

namespace TauCeti

universe u v uH w w'

/-- An `S`-integral model of `Spec H` over `S.integer K`: a finitely presented commutative Hopf
algebra `coordinate` over `S.integer K` together with a generic-fibre bialgebra equivalence with
`H`. -/
structure IntegralModel (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type uH) [CommRing H] [HopfAlgebra K H] (S : Set (HeightOneSpectrum R)) where
  /-- The integral coordinate commutative Hopf algebra over `S.integer K`. -/
  coordinate : _root_.CommHopfAlgCat.{w'} (S.integer K)
  /-- Finite presentation of the integral coordinate algebra over `S.integer K`. -/
  [finitePresentation : Algebra.FinitePresentation (S.integer K) coordinate]
  /-- Identification of the generic fibre `K ⊗[S.integer K] coordinate` with `H`. -/
  baseChangeEquiv : K ⊗[S.integer K] coordinate ≃ₐc[K] H

attribute [instance] IntegralModel.finitePresentation

namespace IntegralModel

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type uH} [CommRing H] [HopfAlgebra K H] {S : Set (HeightOneSpectrum R)}

/-- Because `S.integer K` is Noetherian, any finite-type commutative Hopf algebra over
`S.integer K` with generic fibre `H` defines an `IntegralModel`. -/
def ofFiniteType (C : _root_.CommHopfAlgCat.{w'} (S.integer K))
    [Algebra.FiniteType (S.integer K) C] (e : K ⊗[S.integer K] C ≃ₐc[K] H) :
    IntegralModel R K H S :=
  letI : Algebra.FinitePresentation (S.integer K) C :=
    (Algebra.FinitePresentation.of_finiteType (R := S.integer K) (A := C)).mp inferInstance
  { coordinate := C, baseChangeEquiv := e }

/-- The coordinate algebra of `ofFiniteType C e` is `C`. -/
@[simp]
theorem ofFiniteType_coordinate (C : _root_.CommHopfAlgCat.{w'} (S.integer K))
    [Algebra.FiniteType (S.integer K) C] (e : K ⊗[S.integer K] C ≃ₐc[K] H) :
    (ofFiniteType C e).coordinate = C := (rfl)

/-- The generic-fibre identification of `ofFiniteType C e` agrees with `e` after transport along
`ofFiniteType_coordinate`. -/
theorem ofFiniteType_baseChangeEquiv (C : _root_.CommHopfAlgCat.{w'} (S.integer K))
    [Algebra.FiniteType (S.integer K) C] (e : K ⊗[S.integer K] C ≃ₐc[K] H) :
    (ofFiniteType_coordinate C e ▸ (ofFiniteType C e).baseChangeEquiv) = e := (rfl)

/-- An `R`-model `C₀` of `H` induces an `S`-integral model for every `S` by scalar extension. -/
noncomputable def ofBaseRing (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H) :
    IntegralModel R K H S :=
  letI := Algebra.FiniteType.baseChange (R := R) (A := C₀) (S.integer K)
  ofFiniteType (CommHopfAlgCat.baseChange (K := S.integer K) C₀)
    ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R (S.integer K) C₀ K).trans e)

/-- Canonical `(S.integer K)`-bialgebra equivalence identifying `(ofBaseRing S C₀ e).coordinate`
with `S.integer K ⊗[R] C₀`. -/
noncomputable def ofBaseRingCoordinateEquiv (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H) :
    (ofBaseRing S C₀ e).coordinate ≃ₐc[S.integer K] S.integer K ⊗[R] C₀ :=
  BialgEquiv.refl (S.integer K) (S.integer K ⊗[R] C₀)

/-- Generic-fibre compatibility of `ofBaseRing S C₀ e` with `ofBaseRingCoordinateEquiv` as a
composite of `K`-bialgebra morphisms. -/
theorem ofBaseRing_baseChangeEquiv_comp (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H) :
    ((ofBaseRing S C₀ e).baseChangeEquiv :
        K ⊗[S.integer K] (ofBaseRing S C₀ e).coordinate →ₐc[K] H) =
      (e : K ⊗[R] C₀ →ₐc[K] H).comp
        ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R (S.integer K) C₀ K :
            K ⊗[S.integer K] (S.integer K ⊗[R] C₀) →ₐc[K] K ⊗[R] C₀).comp
          (Bialgebra.TensorProduct.map (BialgHom.id K K)
            (ofBaseRingCoordinateEquiv S C₀ e :
              (ofBaseRing S C₀ e).coordinate →ₐc[S.integer K] S.integer K ⊗[R] C₀))) := by
  apply BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro c m
  rfl

/-- Action of `(ofBaseRing S C₀ e).baseChangeEquiv` on a pure tensor. -/
@[simp]
theorem ofBaseRing_baseChangeEquiv_tmul (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H)
    (c : K) (m : (ofBaseRing S C₀ e).coordinate) :
    (ofBaseRing S C₀ e).baseChangeEquiv (c ⊗ₜ[S.integer K] m) =
      e (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R (S.integer K) C₀ K
        (c ⊗ₜ[S.integer K] ofBaseRingCoordinateEquiv S C₀ e m)) := by
  exact congrArg (fun x ↦ x (c ⊗ₜ[S.integer K] m)) (ofBaseRing_baseChangeEquiv_comp S C₀ e)

/-- The generic-fibre coordinate algebra `H` of `M` is finitely presented over `K`. -/
theorem finitePresentation_genericFiber (M : IntegralModel R K H S) :
    Algebra.FinitePresentation K H :=
  letI := Algebra.FinitePresentation.baseChange (R := S.integer K) (A := M.coordinate) K
  Algebra.FinitePresentation.equiv M.baseChangeEquiv.toAlgEquiv

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is of finite type over `K`. -/
theorem finiteType_genericFiber (M : IntegralModel R K H S) : Algebra.FiniteType K H :=
  have := M.finitePresentation_genericFiber; inferInstance

/-- Canonical ring homomorphism `m ↦ M.baseChangeEquiv (1 ⊗ₜ m)` into `H`. -/
noncomputable def toGenericFiber (M : IntegralModel R K H S) : M.coordinate →+* H :=
  M.baseChangeEquiv.toAlgEquiv.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := S.integer K) (A := K) (B := M.coordinate)).toRingHom

/-- `M.toGenericFiber` sends `m : M.coordinate` to `M.baseChangeEquiv (1 ⊗ₜ m)`. -/
theorem toGenericFiber_apply (M : IntegralModel R K H S) (m : M.coordinate) :
    M.toGenericFiber m = M.baseChangeEquiv (1 ⊗ₜ[S.integer K] m) := (rfl)

/-- On pure tensors `c ⊗ₜ m`, `M.baseChangeEquiv` acts as `c • M.toGenericFiber m`. -/
theorem baseChangeEquiv_tmul (M : IntegralModel R K H S) (c : K) (m : M.coordinate) :
    M.baseChangeEquiv (c ⊗ₜ[S.integer K] m) = c • M.toGenericFiber m := by
  simpa [TensorProduct.smul_tmul', toGenericFiber_apply] using map_smul M.baseChangeEquiv c (1 ⊗ₜ m)

/-- `M.toGenericFiber` sends scalars from `S.integer K` to their images under `algebraMap K H`. -/
@[simp]
theorem toGenericFiber_algebraMap (M : IntegralModel R K H S) (x : S.integer K) :
    M.toGenericFiber (algebraMap (S.integer K) M.coordinate x) = algebraMap K H (x : K) := by
  have h1 : (1 ⊗ₜ[S.integer K] algebraMap (S.integer K) M.coordinate x :
      K ⊗[S.integer K] M.coordinate) = algebraMap K (K ⊗[S.integer K] M.coordinate) (x : K) := by
    rw [← Algebra.TensorProduct.includeRight_apply (R := S.integer K) (A := K),
      Algebra.TensorProduct.includeRight.commutes]
    exact IsScalarTower.algebraMap_apply (S.integer K) K (K ⊗[S.integer K] M.coordinate) x
  rw [toGenericFiber_apply, h1]
  exact M.baseChangeEquiv.toAlgEquiv.commutes (x : K)

/-- Compatibility of `(ofBaseRing S C₀ e).toGenericFiber` with `ofBaseRingCoordinateEquiv` as a
ring homomorphism. -/
theorem toGenericFiber_comp_ofBaseRingCoordinateEquiv_symm (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H) :
    (ofBaseRing S C₀ e).toGenericFiber.comp
        ((ofBaseRingCoordinateEquiv S C₀ e).symm : S.integer K ⊗[R] C₀ ≃+* _).toRingHom =
      (e : K ⊗[R] C₀ →+* H).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (S.integer K) K)
          (AlgHom.id R C₀)).toRingHom := by
  ext x
  · simp [toGenericFiber_apply, ofBaseRing_baseChangeEquiv_tmul, BialgEquiv.apply_symm_apply,
      Subalgebra.smul_def]
  · simp [toGenericFiber_apply, ofBaseRing_baseChangeEquiv_tmul, BialgEquiv.apply_symm_apply]

/-- Under `ofBaseRingCoordinateEquiv`, `(ofBaseRing S C₀ e).toGenericFiber` sends `c ⊗ₜ m` to
`e ((c : K) ⊗ₜ m)`. -/
@[simp]
theorem toGenericFiber_ofBaseRingCoordinateEquiv_symm_tmul (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H)
    (c : S.integer K) (m : C₀) :
    (ofBaseRing S C₀ e).toGenericFiber
        ((ofBaseRingCoordinateEquiv S C₀ e).symm (c ⊗ₜ[R] m)) =
      e ((c : K) ⊗ₜ[R] m) := by
  rw [toGenericFiber_apply, ofBaseRing_baseChangeEquiv_tmul, BialgEquiv.apply_symm_apply,
    Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul, Subalgebra.smul_def, smul_eq_mul,
    mul_one]

/-- Any integral model admits a finite `(S.integer K)`-algebra generating set for
`M.coordinate`. -/
theorem exists_finset_adjoin_eq_top (M : IntegralModel R K H S) :
    ∃ F : Finset M.coordinate,
      Algebra.adjoin (S.integer K) (Set.range ((↑) : F → M.coordinate)) = ⊤ := by
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := S.integer K) (A := M.coordinate)
  exact ⟨F, by simpa using hF⟩

/-- Canonical group isomorphism identifying `A`-valued `(S.integer K)`-points of `M.coordinate`
with `A`-valued `K`-points of `H`, for any commutative `K`-algebra `A`. -/
noncomputable def pointsMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
    (BialgEquiv.mapDomainMulEquiv (A := A) M.baseChangeEquiv).symm

/-- Restricting a `K`-point `g` along `(M.pointsMulEquiv A).symm` evaluates `g` on
`M.toGenericFiber`. -/
@[simp]
theorem pointsMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (g : WithConv (H →ₐ[K] A)) (m : M.coordinate) :
    ((M.pointsMulEquiv A).symm g).ofConv m = g.ofConv (M.toGenericFiber m) := by
  simp [pointsMulEquiv, toGenericFiber_apply]

/-- Evaluating `M.pointsMulEquiv A x` at `M.toGenericFiber m` recovers `x.ofConv m`. -/
@[simp]
theorem pointsMulEquiv_apply_ofConv_toGenericFiber (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) (m : M.coordinate) :
    (M.pointsMulEquiv A x).ofConv (M.toGenericFiber m) = x.ofConv m := by
  simpa using (M.pointsMulEquiv_symm_apply_ofConv (M.pointsMulEquiv A x) m).symm

/-- Evaluating `M.pointsMulEquiv A x` on `M.baseChangeEquiv (c ⊗ₜ m)` gives `c • x.ofConv m`. -/
theorem pointsMulEquiv_apply_ofConv_baseChangeEquiv (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) (c : K) (m : M.coordinate) :
    (M.pointsMulEquiv A x).ofConv (M.baseChangeEquiv (c ⊗ₜ[S.integer K] m)) = c • x.ofConv m := by
  rw [M.baseChangeEquiv_tmul, map_smul, M.pointsMulEquiv_apply_ofConv_toGenericFiber]

/-- Canonical injective homomorphism from `B`-valued `(S.integer K)`-points of `M.coordinate`
to `A`-valued `K`-points of `H`, for an `(S.integer K)`-subalgebra `B` of a commutative `K`-algebra
`A`. -/
noncomputable def subalgebraPointsHom (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] (B : Subalgebra (S.integer K) A) :
    WithConv (M.coordinate →ₐ[S.integer K] B) →* WithConv (H →ₐ[K] A) :=
  (M.pointsMulEquiv A).toMonoidHom.comp (AlgHom.mapValue (H := M.coordinate) B.val)

/-- `M.subalgebraPointsHom B` is injective. -/
theorem subalgebraPointsHom_injective (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] (B : Subalgebra (S.integer K) A) :
    Function.Injective (M.subalgebraPointsHom B) :=
  (M.pointsMulEquiv A).injective.comp (AlgHom.mapValue_injective Subtype.val_injective)

/-- Evaluating `M.subalgebraPointsHom B x` at `M.toGenericFiber m` returns `(x.ofConv m : A)`. -/
@[simp]
theorem subalgebraPointsHom_apply_ofConv_toGenericFiber (M : IntegralModel R K H S) {A : Type w}
    [CommRing A] [Algebra K A] (B : Subalgebra (S.integer K) A)
    (x : WithConv (M.coordinate →ₐ[S.integer K] B)) (m : M.coordinate) :
    (M.subalgebraPointsHom B x).ofConv (M.toGenericFiber m) = (x.ofConv m : A) := by
  simp [subalgebraPointsHom]

/-- Subgroup of `WithConv (H →ₐ[K] A)` of points arising from `B`-valued `(S.integer K)`-points of
`M.coordinate`, for an `(S.integer K)`-subalgebra `B : Subalgebra (S.integer K) A`. -/
noncomputable def subalgebraPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] (B : Subalgebra (S.integer K) A) : Subgroup (WithConv (H →ₐ[K] A)) :=
  (M.subalgebraPointsHom B).range

/-- `g ∈ M.subalgebraPoints B` iff `g` sends every integral coordinate `M.toGenericFiber m` into
`B`. -/
@[simp]
theorem mem_subalgebraPoints_iff (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] (B : Subalgebra (S.integer K) A) {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subalgebraPoints B ↔ ∀ m : M.coordinate, g.ofConv (M.toGenericFiber m) ∈ B := by
  rw [subalgebraPoints, subalgebraPointsHom, MonoidHom.range_comp, Subgroup.mem_map_equiv,
    MonoidHom.mem_range, ← MonoidHom.mem_mrange,
    AlgHom.mem_mrange_mapValue_iff Subtype.val_injective]
  refine forall_congr' fun m ↦ ?_
  rw [M.pointsMulEquiv_symm_apply_ofConv, AlgHom.mem_range]
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

/-- For an `S'`-integral model whose coordinate algebra is equivalent to `S'.integer K ⊗[k₀] C`
sending `c ⊗ₜ m` under `toGenericFiber` to `(c : K) • gen m`, membership in `subalgebraPoints B`
reduces to evaluating on the generators `gen m`. -/
theorem mem_subalgebraPoints_iff_of_tensorEquiv {S' : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S') {k₀ C : Type*} [CommRing k₀] [Semiring C]
    [Algebra k₀ (S'.integer K)] [Algebra k₀ C]
    (eCoord : M.coordinate ≃ₐ[S'.integer K] S'.integer K ⊗[k₀] C) (gen : C → H)
    (hgen : ∀ (c : S'.integer K) (m : C),
      M.toGenericFiber (eCoord.symm (c ⊗ₜ[k₀] m)) = (c : K) • gen m)
    {A : Type w} [CommRing A] [Algebra K A] (B : Subalgebra (S'.integer K) A)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subalgebraPoints B ↔ ∀ m : C, g.ofConv (gen m) ∈ B := by
  rw [mem_subalgebraPoints_iff]
  refine ⟨fun h m ↦ ?_, fun h t ↦ ?_⟩
  · simpa only [hgen 1 m, Subalgebra.coe_one, one_smul] using h (eCoord.symm (1 ⊗ₜ[k₀] m))
  · rw [← eCoord.symm_apply_apply t]
    refine TensorProduct.induction_one_tmul (σ := algebraMap (S'.integer K) K)
      (P := fun x ↦ g.ofConv x ∈ B)
      (fun x ↦ M.toGenericFiber (eCoord.symm x))
      (fun _ _ ↦ by rw [map_add, map_add])
      (fun c m ↦ by simp only [hgen, Subalgebra.coe_one, one_smul, Subalgebra.algebraMap_apply])
      (fun m ↦ by simpa only [hgen, Subalgebra.coe_one, one_smul] using h m)
      (fun c _ hx ↦ by
        rw [map_smul, Algebra.smul_def]
        exact B.mul_mem (B.algebraMap_algebraMap_mem (S := K) c) hx)
      (fun hx hy ↦ by rw [map_add]; exact B.add_mem hx hy)
      _

/-- Membership in `M.subalgebraPoints B` reduces to an `(S.integer K)`-algebra generating
family. -/
theorem mem_subalgebraPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (B : Subalgebra (S.integer K) A)
    {ι : Type*} {a : ι → M.coordinate} (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subalgebraPoints B ↔ ∀ i, g.ofConv (M.toGenericFiber (a i)) ∈ B := by
  rw [mem_subalgebraPoints_iff]
  refine ⟨fun h i ↦ h (a i), fun h m ↦ ?_⟩
  have hm : m ∈ Algebra.adjoin (S.integer K) (Set.range a) := ha ▸ Algebra.mem_top
  induction hm using Algebra.adjoin_induction with
  | mem _ hx => rcases hx with ⟨i, rfl⟩; exact h i
  | algebraMap x =>
    rw [M.toGenericFiber_algebraMap, g.ofConv.commutes]
    exact B.algebraMap_algebraMap_mem (S := K) x
  | add _ _ _ _ hx hy => rw [map_add, map_add]; exact B.add_mem hx hy
  | mul _ _ _ _ hx hy => rw [map_mul, map_mul]; exact B.mul_mem hx hy

/-- Canonical topological group isomorphism identifying `A`-valued `(S.integer K)`-points of
`M.coordinate` with `A`-valued `K`-points of `H` for a commutative topological `K`-algebra `A`. -/
noncomputable def pointsContinuousMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃ₜ* WithConv (H →ₐ[K] A) where
  toMulEquiv := M.pointsMulEquiv A
  continuous_toFun := ((BialgHom.continuous_mapDomain M.baseChangeEquiv.symm.toBialgHom).comp
    (AlgHom.continuous_baseChangePointsMulEquiv (k := S.integer K) (K := K))).congr
    fun _ ↦ by simp [pointsMulEquiv]
  continuous_invFun := continuous_withConv_iff.2 fun m ↦ by
    simpa only [MulEquiv.invFun_eq_symm, M.pointsMulEquiv_symm_apply_ofConv] using
      continuous_eval_ofConv (M.toGenericFiber m)

/-- The underlying `MulEquiv` of `M.pointsContinuousMulEquiv A` is `M.pointsMulEquiv A`. -/
@[simp]
theorem coe_pointsContinuousMulEquiv (M : IntegralModel R K H S) (A : Type w) [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    (M.pointsContinuousMulEquiv A :
      WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A)) =
      M.pointsMulEquiv A := (rfl)

/-- The forward map of `M.pointsContinuousMulEquiv A` is `M.pointsMulEquiv A`. -/
@[simp]
theorem pointsContinuousMulEquiv_apply (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) :
    M.pointsContinuousMulEquiv A x = M.pointsMulEquiv A x := (rfl)

/-- The inverse map of `M.pointsContinuousMulEquiv A` is `(M.pointsMulEquiv A).symm`. -/
@[simp]
theorem pointsContinuousMulEquiv_symm_apply (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] (g : WithConv (H →ₐ[K] A)) :
    (M.pointsContinuousMulEquiv A).symm g = (M.pointsMulEquiv A).symm g := (rfl)

/-- When `B` is open in `A`, `M.subalgebraPoints B` is open in `WithConv (H →ₐ[K] A)`. -/
theorem isOpen_subalgebraPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subalgebra (S.integer K) A)
    (hBopen : IsOpen (B : Set A)) :
    IsOpen (M.subalgebraPoints B : Set (WithConv (H →ₐ[K] A))) :=
  ((M.pointsContinuousMulEquiv A).toHomeomorph.isOpenEmbedding.comp
    (AlgHom.isOpenEmbedding_mapValue (ψ := B.val) hBopen.isOpenEmbedding_subtypeVal)).isOpen_range

/-- When `B` is closed in `A`, `M.subalgebraPoints B` is closed in `WithConv (H →ₐ[K] A)`. -/
theorem isClosed_subalgebraPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subalgebra (S.integer K) A)
    (hBclosed : IsClosed (B : Set A)) :
    IsClosed (M.subalgebraPoints B : Set (WithConv (H →ₐ[K] A))) :=
  ((M.pointsContinuousMulEquiv A).toHomeomorph.isClosedEmbedding.comp
    (AlgHom.isClosedEmbedding_mapValue (ψ := B.val)
      hBclosed.isClosedEmbedding_subtypeVal)).isClosed_range

/-- When `B` is compact inside a T1 topological ring `A`, `M.subalgebraPoints B` is compact. -/
theorem isCompact_subalgebraPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T1Space A]
    (B : Subalgebra (S.integer K) A) [CompactSpace B] :
    IsCompact (M.subalgebraPoints B : Set (WithConv (H →ₐ[K] A))) :=
  isCompact_range ((M.pointsContinuousMulEquiv A).continuous.comp
    (AlgHom.continuous_mapValue (ψ := B.val) continuous_subtypeVal))

/-- For `v ∉ S`, `M.localPoints v hv` is the subgroup `𝒢(𝒪_v) ≤ G(K_v)` of `v`-integral points. -/
noncomputable def localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    (hv : v ∉ S) : Subgroup (AdelicPoints.LocalPoints R K H v) :=
  M.subalgebraPoints (v.adicCompletionIntegersSubalgebra K S hv)

/-- `g ∈ M.localPoints v hv` iff `g` evaluates every integral coordinate into `𝒪_v`. -/
@[simp]
theorem mem_localPoints_iff (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : AdelicPoints.LocalPoints R K H v} :
    g ∈ M.localPoints v hv ↔
      ∀ m : M.coordinate, g.ofConv (M.toGenericFiber m) ∈ v.adicCompletionIntegers K := by
  rw [localPoints]
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegersSubalgebra] using
    M.mem_subalgebraPoints_iff (v.adicCompletionIntegersSubalgebra K S hv)

/-- Membership in `M.localPoints v hv` reduces to an `(S.integer K)`-algebra generating family. -/
theorem mem_localPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {v : HeightOneSpectrum R} (hv : v ∉ S) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤)
    {g : AdelicPoints.LocalPoints R K H v} :
    g ∈ M.localPoints v hv ↔
      ∀ i, g.ofConv (M.toGenericFiber (a i)) ∈ v.adicCompletionIntegers K := by
  rw [localPoints]
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegersSubalgebra] using
    M.mem_subalgebraPoints_iff_of_adjoin_eq_top (v.adicCompletionIntegersSubalgebra K S hv) ha

/-- For `v ∉ S`, `g ∈ (ofBaseRing S C₀ e).localPoints v hv` iff `g` evaluates every base-ring
coordinate `e (1 ⊗ₜ[R] m)` into `𝒪_v`. -/
@[simp high]
theorem mem_localPoints_ofBaseRing_iff (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H)
    {v : HeightOneSpectrum R} (hv : v ∉ S) {g : AdelicPoints.LocalPoints R K H v} :
    g ∈ (ofBaseRing S C₀ e).localPoints v hv ↔
      ∀ m : C₀, g.ofConv (e (1 ⊗ₜ[R] m)) ∈ v.adicCompletionIntegers K := by
  rw [localPoints, mem_subalgebraPoints_iff_of_tensorEquiv (ofBaseRing S C₀ e)
    (ofBaseRingCoordinateEquiv S C₀ e).toAlgEquiv (fun m ↦ e (1 ⊗ₜ[R] m))
    (fun c m ↦ (toGenericFiber_ofBaseRingCoordinateEquiv_symm_tmul S C₀ e c m).trans (by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]))]
  simp [HeightOneSpectrum.mem_adicCompletionIntegersSubalgebra]

/-- `M.localPoints v hv` is an open subgroup of `AdelicPoints.LocalPoints R K H v`. -/
theorem isOpen_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsOpen (M.localPoints v hv : Set (AdelicPoints.LocalPoints R K H v)) :=
  M.isOpen_subalgebraPoints (v.adicCompletionIntegersSubalgebra K S hv)
    (by rw [HeightOneSpectrum.coe_adicCompletionIntegersSubalgebra]
        exact Valued.isOpen_valuationSubring _)

/-- `M.localPoints v hv` is closed in `AdelicPoints.LocalPoints R K H v`. -/
theorem isClosed_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsClosed (M.localPoints v hv : Set (AdelicPoints.LocalPoints R K H v)) :=
  Subgroup.isClosed_of_isOpen (M.localPoints v hv) (M.isOpen_localPoints v hv)

/-- When `R ⧸ v.asIdeal` is finite, `M.localPoints v hv` is compact. -/
theorem isCompact_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] (hv : v ∉ S) :
    IsCompact (M.localPoints v hv : Set (AdelicPoints.LocalPoints R K H v)) := by
  have hset : (v.adicCompletionIntegersSubalgebra K S hv : Set (v.adicCompletion K)) =
      Set.range ((↑) : v.adicCompletionIntegers K → v.adicCompletion K) := by
    rw [HeightOneSpectrum.coe_adicCompletionIntegersSubalgebra, Subtype.range_coe]
  let _ : CompactSpace (v.adicCompletionIntegersSubalgebra K S hv) :=
    isCompact_iff_compactSpace.mp (hset ▸ isCompact_range continuous_subtypeVal)
  exact M.isCompact_subalgebraPoints (v.adicCompletionIntegersSubalgebra K S hv)

open scoped Classical in
/-- Reference subgroup family across finite places: `M.localPoints v hv` outside `S`, `⊤` on `S`. -/
noncomputable def level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    Subgroup (AdelicPoints.LocalPoints R K H v) := if hv : v ∈ S then ⊤ else M.localPoints v hv

/-- At `v ∈ S`, `M.level v = ⊤`. -/
@[simp]
theorem level_of_mem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∈ S) :
    M.level v = ⊤ := by simp [level, hv]

/-- At `v ∉ S`, `M.level v = M.localPoints v hv`. -/
@[simp]
theorem level_of_notMem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    M.level v = M.localPoints v hv := by simp [level, hv]

/-- Every reference subgroup `M.level v` is open in `AdelicPoints.LocalPoints R K H v`. -/
theorem isOpen_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsOpen (M.level v : Set (AdelicPoints.LocalPoints R K H v)) := by
  by_cases hv : v ∈ S <;> simp [hv, M.isOpen_localPoints]

/-- Every reference subgroup `M.level v` is closed in `AdelicPoints.LocalPoints R K H v`. -/
theorem isClosed_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsClosed (M.level v : Set (AdelicPoints.LocalPoints R K H v)) :=
  Subgroup.isClosed_of_isOpen (M.level v) (M.isOpen_level v)

/-- `M.level v` bundled as an `OpenSubgroup` of `AdelicPoints.LocalPoints R K H v`. -/
noncomputable def openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    OpenSubgroup (AdelicPoints.LocalPoints R K H v) := ⟨M.level v, M.isOpen_level v⟩

/-- The underlying `Subgroup` of `M.openLevel v` is `M.level v`. -/
@[simp]
theorem coe_openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    (M.openLevel v : Subgroup (AdelicPoints.LocalPoints R K H v)) = M.level v := (rfl)

/-- Membership in `M.openLevel v` agrees with membership in `M.level v`. -/
@[simp]
theorem mem_openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    {g : AdelicPoints.LocalPoints R K H v} : g ∈ M.openLevel v ↔ g ∈ M.level v := Iff.rfl

/-- For `S = ∅` and finite residue fields, `M.localPoints` packages as `CompactOpenSubgroups`. -/
noncomputable def compactOpenSubgroups (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    CompactOpenSubgroups (AdelicPoints.LocalPoints R K H) where
  subgroup v := M.openLevel v
  isCompact_subgroup v := by
    rw [← OpenSubgroup.coe_toSubgroup, M.coe_openLevel, M.level_of_notMem (Set.notMem_empty v)]
    exact M.isCompact_localPoints v (Set.notMem_empty v)

/-- At `v`, `M.compactOpenSubgroups.subgroup v` is `M.openLevel v`. -/
@[simp]
theorem compactOpenSubgroups_subgroup (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] (v : HeightOneSpectrum R) :
    M.compactOpenSubgroups.subgroup v = M.openLevel v := (rfl)

/-- For `T ⊇ S`, `M.globalPoints T hST` is the subgroup `𝒢(𝒪_{K,T}) ≤ G(K)` of `T`-integral
`K`-rational points. -/
noncomputable def globalPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : Subgroup (WithConv (H →ₐ[K] K)) :=
  M.subalgebraPoints (Set.integerSubalgebra K hST)

/-- `g ∈ M.globalPoints T hST` iff its values on `M.toGenericFiber` lie in `T.integer K`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ m : M.coordinate, g.ofConv (M.toGenericFiber m) ∈ T.integer K := by
  rw [globalPoints]
  simpa only [Set.mem_integerSubalgebra] using
    M.mem_subalgebraPoints_iff (Set.integerSubalgebra K hST)

/-- Enlarging `T` enlarges `M.globalPoints`. -/
theorem globalPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.globalPoints T₁ hST₁ ≤ M.globalPoints T₂ (hST₁.trans hT₁₂) := fun _ hg ↦
  (mem_globalPoints_iff M _).mpr fun m ↦
    Set.integer_mono K hT₁₂ ((mem_globalPoints_iff M _).mp hg m)

/-- Local-global characterization: `g ∈ M.globalPoints T hST` iff its image in `G(K_v)` lies in
`M.localPoints v` for all `v ∉ T`. -/
theorem mem_globalPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
      (AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K)) g :
          AdelicPoints.LocalPoints R K H v) ∈
        M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_globalPoints_iff, Set.mem_integer_iff, mem_localPoints_iff,
    AlgHom.mapValue_apply, AlgHom.comp_apply, Algebra.ofId_apply,
    HeightOneSpectrum.algebraMap_mem_adicCompletionIntegers_iff]
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

section Enlarge

variable {S' : Set (HeightOneSpectrum R)}

/-- Scalar extension along `S.integer K → S'.integer K` (`S ⊆ S'`) produces an `S'`-integral model
whose generic-fibre identification factors through `baseChangeTowerBialgEquiv`. -/
noncomputable def enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S') : IntegralModel R K H S' :=
  letI := integerInclusionAlgebra K hSS'; haveI := isScalarTower_integerInclusionAlgebra K hSS'
  letI := Algebra.FinitePresentation.baseChange (R := S.integer K) (A := M.coordinate)
    (S'.integer K)
  { coordinate := CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate
    baseChangeEquiv := (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
      (S.integer K) (S'.integer K) M.coordinate K).trans M.baseChangeEquiv }

/-- Canonical `S'.integer K`-bialgebra equivalence identifying `(M.enlarge hSS').coordinate`
with `S'.integer K ⊗[S.integer K] M.coordinate`. -/
noncomputable def enlargeCoordinateEquiv (M : IntegralModel R K H S) (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra K hSS'
    (M.enlarge hSS').coordinate ≃ₐc[S'.integer K] S'.integer K ⊗[S.integer K] M.coordinate :=
  letI := integerInclusionAlgebra K hSS'
  BialgEquiv.refl (S'.integer K) (S'.integer K ⊗[S.integer K] M.coordinate)

/-- Generic-fibre compatibility of `M.enlarge hSS'` with `enlargeCoordinateEquiv` as a composite
of `K`-bialgebra morphisms. -/
theorem enlarge_baseChangeEquiv_comp (M : IntegralModel R K H S) (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
    (M.enlarge hSS').baseChangeEquiv.toBialgHom =
      M.baseChangeEquiv.toBialgHom.comp
        ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
            (S.integer K) (S'.integer K) M.coordinate K).toBialgHom.comp
          (Bialgebra.TensorProduct.map (BialgHom.id K K)
            (M.enlargeCoordinateEquiv hSS').toBialgHom)) := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  apply BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro c m
  rfl

/-- Action of `(M.enlarge hSS').baseChangeEquiv` on a pure tensor via `enlargeCoordinateEquiv`. -/
@[simp]
theorem enlarge_baseChangeEquiv_tmul (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (c : K) (m : (M.enlarge hSS').coordinate) :
    letI := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
    (M.enlarge hSS').baseChangeEquiv (c ⊗ₜ[S'.integer K] m) =
      M.baseChangeEquiv (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
        (S.integer K) (S'.integer K) M.coordinate K
        (c ⊗ₜ[S'.integer K] M.enlargeCoordinateEquiv hSS' m)) := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  exact congrArg (fun x ↦ x (c ⊗ₜ[S'.integer K] m)) (M.enlarge_baseChangeEquiv_comp hSS')

/-- Evaluation of `(M.enlarge hSS').baseChangeEquiv` on pure tensors coming from
`enlargeCoordinateEquiv.symm`. -/
theorem enlarge_baseChangeEquiv_tmul_symm (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (c₁ : K) (c₂ : S'.integer K) (m : M.coordinate) :
    letI := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
    (M.enlarge hSS').baseChangeEquiv
        (c₁ ⊗ₜ[S'.integer K] (M.enlargeCoordinateEquiv hSS').symm (c₂ ⊗ₜ[S.integer K] m)) =
      M.baseChangeEquiv (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
        (S.integer K) (S'.integer K) M.coordinate K
        (c₁ ⊗ₜ[S'.integer K] (c₂ ⊗ₜ[S.integer K] m))) := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  rw [M.enlarge_baseChangeEquiv_tmul hSS', BialgEquiv.apply_symm_apply]

/-- Compatibility of `(M.enlarge hSS').toGenericFiber` with `enlargeCoordinateEquiv` as a ring
homomorphism. -/
theorem toGenericFiber_comp_enlargeCoordinateEquiv_symm (M : IntegralModel R K H S)
    (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
    (M.enlarge hSS').toGenericFiber.comp
        ((M.enlargeCoordinateEquiv hSS').symm :
          S'.integer K ⊗[S.integer K] M.coordinate ≃+* _).toRingHom =
      M.baseChangeEquiv.toAlgEquiv.toRingHom.comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (S.integer K) (S'.integer K) K)
          (AlgHom.id (S.integer K) M.coordinate)).toRingHom := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  apply Algebra.TensorProduct.ringHom_ext
  · ext x
    simp [toGenericFiber_apply, M.enlarge_baseChangeEquiv_tmul_symm hSS', Subalgebra.smul_def]
  · ext m
    simp [toGenericFiber_apply, M.enlarge_baseChangeEquiv_tmul_symm hSS']

/-- Under `enlargeCoordinateEquiv`, `(M.enlarge hSS').toGenericFiber` sends a pure tensor `c ⊗ₜ m`
to `(c : K) • M.toGenericFiber m`. -/
@[simp]
theorem toGenericFiber_enlargeCoordinateEquiv_symm_tmul (M : IntegralModel R K H S)
    (hSS' : S ⊆ S') (c : S'.integer K) (m : M.coordinate) :
    letI := integerInclusionAlgebra K hSS'
    (M.enlarge hSS').toGenericFiber ((M.enlargeCoordinateEquiv hSS').symm (c ⊗ₜ[S.integer K] m)) =
      (c : K) • M.toGenericFiber m := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  rw [(M.enlarge hSS').toGenericFiber_apply, M.enlarge_baseChangeEquiv_tmul_symm hSS',
    Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul, Subalgebra.smul_def,
    smul_eq_mul, mul_one, M.baseChangeEquiv_tmul]

/-- Enlarging `S` to `S'` preserves `subalgebraPoints` for subalgebras with equal underlying
sets. -/
theorem subalgebraPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {A : Type w} [CommRing A] [Algebra K A] (B' : Subalgebra (S'.integer K) A)
    (B : Subalgebra (S.integer K) A) (hBB' : (B : Set A) = (B' : Set A)) :
    letI := integerInclusionAlgebra K hSS'
    (M.enlarge hSS').subalgebraPoints B' = M.subalgebraPoints B := by
  let := integerInclusionAlgebra K hSS'
  ext g
  rw [mem_subalgebraPoints_iff_of_tensorEquiv (M.enlarge hSS')
      (M.enlargeCoordinateEquiv hSS').toAlgEquiv M.toGenericFiber
      (fun c m ↦ M.toGenericFiber_enlargeCoordinateEquiv_symm_tmul hSS' c m),
    mem_subalgebraPoints_iff]
  simp only [← SetLike.mem_coe, hBB']

/-- Enlarging `S` to `S'` leaves `localPoints` unchanged at every place `v ∉ S'`. -/
@[simp]
theorem localPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (v : HeightOneSpectrum R) (hv : v ∉ S') :
    (M.enlarge hSS').localPoints v hv = M.localPoints v (fun hvS ↦ hv (hSS' hvS)) :=
  M.subalgebraPoints_enlarge hSS' _ _ (by simp)

/-- Enlarging `S` to `S'` leaves `level v` unchanged at every place `v ∉ S'`. -/
theorem level_enlarge_of_notMem (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {v : HeightOneSpectrum R} (hv : v ∉ S') : (M.enlarge hSS').level v = M.level v := by
  rw [(M.enlarge hSS').level_of_notMem hv, M.level_of_notMem (fun hvS ↦ hv (hSS' hvS)),
    M.localPoints_enlarge hSS' v hv]

/-- Enlarging `S` to `S'` leaves `globalPoints T` unchanged for every `T ⊇ S'`. -/
@[simp]
theorem globalPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').globalPoints T hS'T = M.globalPoints T (hSS'.trans hS'T) :=
  M.subalgebraPoints_enlarge hSS' _ _ (by simp)

end Enlarge

/-- For every fixed `h : H`, at all but finitely many places `v`, if `v ∉ S` then every
`g ∈ M.localPoints v hv` evaluates `h` into `v.adicCompletionIntegers K`. -/
theorem eventually_localPoints_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (h : H) :
    ∀ᶠ v in cofinite, ∀ (hv : v ∉ S), ∀ g ∈ M.localPoints v hv,
      g.ofConv h ∈ v.adicCompletionIntegers K := by
  rw [← M.baseChangeEquiv.apply_symm_apply h]
  refine TensorProduct.induction_tmul_smul (K := S.integer K) (L := K)
    (P := fun z ↦ ∀ᶠ v in cofinite, ∀ (hv : v ∉ S), ∀ g ∈ M.localPoints v hv,
      g.ofConv (M.baseChangeEquiv z) ∈ v.adicCompletionIntegers K)
    (one_tmul := fun m ↦ Filter.Eventually.of_forall fun v hv g hg ↦ by
      rw [M.baseChangeEquiv_tmul, one_smul]
      exact (M.mem_localPoints_iff hv).mp hg m)
    (smul := fun c _ hx ↦ by
      filter_upwards [(algebraMap K (FiniteAdeleRing R K) c).property, hx] with v hc hxv hv g hg
      rw [map_smul, map_smul, Algebra.smul_def]
      exact mul_mem hc (hxv hv g hg))
    (add := fun hx hy ↦ by
      filter_upwards [hx, hy] with v hvx hvy hv g hg
      rw [map_add, map_add]
      exact add_mem (hvx hv g hg) (hvy hv g hg))
    (M.baseChangeEquiv.symm h)

/-- When `S` is finite, for every `h : H`, eventually every `g ∈ M.level v` maps `h` into `𝒪_v`. -/
theorem eventually_level_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (hS : S.Finite) (h : H) :
    ∀ᶠ v in cofinite, ∀ g ∈ M.level v, g.ofConv h ∈ v.adicCompletionIntegers K := by
  filter_upwards [hS.compl_mem_cofinite, M.eventually_localPoints_ofConv_mem h] with v hv hloc g hg
  rw [M.level_of_notMem hv] at hg; exact hloc hv g hg

/-- If `S₁` is finite, then `M₁.level v ≤ M₂.level v` at all but finitely many places `v`. -/
theorem level_eventuallyLE {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂) (hS₁ : S₁.Finite) :
    ∀ᶠ v in cofinite, M₁.level v ≤ M₂.level v := by
  obtain ⟨F, hgen⟩ := M₂.exists_finset_adjoin_eq_top
  filter_upwards [eventually_all.mpr fun i : F ↦
    M₁.eventually_level_ofConv_mem hS₁ (M₂.toGenericFiber i)] with v hv g hg
  by_cases hv₂ : v ∈ S₂
  · rw [M₂.level_of_mem hv₂]; exact Subgroup.mem_top g
  · rw [M₂.level_of_notMem hv₂, M₂.mem_localPoints_iff_of_adjoin_eq_top hv₂ hgen]
    exact fun i ↦ hv i g hg

/-- Independence of the integral model away from finitely many places (Conrad 2012, Prop. 3.3). -/
theorem level_eventuallyEq {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) : ∀ᶠ v in cofinite, M₁.level v = M₂.level v := by
  filter_upwards [level_eventuallyLE M₁ M₂ hS₁, level_eventuallyLE M₂ M₁ hS₂] with _ h₁₂ h₂₁
  exact le_antisymm h₁₂ h₂₁

/-- Canonical `S`-integral model of `Spec K`, with coordinate ring `S.integer K`. -/
noncomputable def trivial (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (S : Set (HeightOneSpectrum R)) :
    IntegralModel R K K S where
  coordinate := _root_.CommHopfAlgCat.of (S.integer K) (S.integer K)
  baseChangeEquiv :=
    BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.rid (S.integer K) K K) (by ext) (by ext)

/-- Canonical `(S.integer K)`-algebra equivalence identifying `(trivial R K S).coordinate` with
`S.integer K`. -/
noncomputable def trivialCoordinateEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (S : Set (HeightOneSpectrum R)) :
    (trivial R K S).coordinate ≃ₐ[S.integer K] S.integer K :=
  AlgEquiv.refl

/-- Action of `(trivial R K S).baseChangeEquiv` on a pure tensor. -/
@[simp]
theorem trivial_baseChangeEquiv_tmul (c : K) (m : (trivial R K S).coordinate) :
    (trivial R K S).baseChangeEquiv (c ⊗ₜ[S.integer K] m) =
      Algebra.TensorProduct.rid (S.integer K) K K
        (c ⊗ₜ[S.integer K] trivialCoordinateEquiv R K S m) := (rfl)

/-- `(trivial R K S).toGenericFiber` sends `m` to `(trivialCoordinateEquiv R K S m : K)`. -/
@[simp]
theorem trivial_toGenericFiber (x : (trivial R K S).coordinate) :
    (trivial R K S).toGenericFiber x = (trivialCoordinateEquiv R K S x : K) := by
  rw [toGenericFiber_apply, trivial_baseChangeEquiv_tmul, Algebra.TensorProduct.rid_tmul,
    Subalgebra.smul_def, smul_eq_mul, mul_one]

/-- Every `A`-valued `K`-point of `Spec K` evaluates `(trivial R K S).toGenericFiber m` via
`algebraMap K A`. -/
theorem trivial_ofConv_toGenericFiber {A : Type w} [CommRing A] [Algebra K A]
    (g : WithConv (K →ₐ[K] A)) (m : (trivial R K S).coordinate) :
    g.ofConv ((trivial R K S).toGenericFiber m) =
      algebraMap K A (trivialCoordinateEquiv R K S m : K) := by
  have hcomm := g.ofConv.commutes (trivialCoordinateEquiv R K S m : K)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at hcomm
  rw [trivial_toGenericFiber, hcomm]

/-- Every `A`-valued `K`-point of `Spec K` lies in `(trivial R K S).subalgebraPoints B` for any
`(S.integer K)`-subalgebra `B` of `A`. -/
@[simp]
theorem subalgebraPoints_trivial {A : Type w} [CommRing A] [Algebra K A]
    (B : Subalgebra (S.integer K) A) :
    (trivial R K S).subalgebraPoints B = ⊤ := by
  rw [eq_top_iff]; intro g _
  rw [mem_subalgebraPoints_iff]; intro m
  rw [trivial_ofConv_toGenericFiber]
  exact B.algebraMap_algebraMap_mem (S := K) _

/-- Every `v`-adic point of `Spec K` is integral at `v ∉ S`. -/
@[simp]
theorem localPoints_trivial (v : HeightOneSpectrum R) (hv : v ∉ S) :
    (trivial R K S).localPoints v hv = ⊤ :=
  subalgebraPoints_trivial _

/-- Every `K`-rational point of `Spec K` is `T`-integral for any `T ⊇ S`. -/
@[simp]
theorem globalPoints_trivial (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) :
    (trivial R K S).globalPoints T hST = ⊤ :=
  subalgebraPoints_trivial _

end IntegralModel

end TauCeti
