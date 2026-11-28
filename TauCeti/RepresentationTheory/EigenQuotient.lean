/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Eigenquotients of families of representations

Let `K → L` be an algebra over a commutative ring, `Γ` a monoid and `ρ i` representations of `Γ`
on `K`-modules `V i`, indexed by `i : ι`, each with a family of `K`-linear operators `T i s`
(`s : S`), and let `θ : S → L`. A family of `K`-linear maps `G i : V i → W` into an
`L`-representation `σ` of `Γ` is an *eigenfamily* (`TauCeti.IsEigenFamily`) if every `G i` is
`Γ`-equivariant and `G i ∘ T i s = θ s • G i`. An *eigenquotient* (`TauCeti.IsEigenQuotient`) is
an eigenfamily `F i : V i → L^N` into a representation `r` on `L^N` whose images span `L^N` over
`L` and through which every eigenfamily into an `L`-representation factors uniquely by an
`L`-linear map. Thus `r` is the largest quotient of the scalar extension of `⨁ i, V i` to `L` on
which every `T i s` acts by `θ s`. The number `N` may be `0`, for instance when no nonzero
eigenfamily exists.

When `L` is a field, `ι` is finite and every `V i` is a finite `K`-module, an eigenquotient exists
(`TauCeti.exists_isEigenQuotient`). It is the quotient of `L ⊗[K] ⨁ i, V i` by the `L`-span of
the `Γ`-translates of the elements `1 ⊗ T i s x - θ s • (1 ⊗ x)`, with the scalar extension
`Representation.baseChange` of `Representation.directSum ρ`, read in a basis. No
compatibility between the operators `T i s` and the action of `Γ` is needed; when the `T i s`
commute with `Γ`, the span of the elements `1 ⊗ T i s x - θ s • (1 ⊗ x)` is already
`Γ`-stable.

Continuity is that of matrix coefficients: `g ↦ f (ρ i g x)` is continuous for every `K`-linear
form `f` (`TauCeti.ContinuousRep.ofMatrixCoeff` turns this into joint continuity for the module
topology). Suppose that addition on `L` and scalar multiplication `K × L → L` are continuous.
If every `V i` is finite free over `K` with
continuous matrix coefficients, then the matrix coefficients `g ↦ l (r g y)` of every
eigenquotient are continuous (`TauCeti.IsEigenQuotient.continuous_apply`).

## Main definitions

* `TauCeti.IsEigenFamily`: equivariant maps on which the operators act by the given eigenvalues.
* `TauCeti.IsEigenQuotient`: the universal eigenfamily into a representation on `L^N`.

## Main results

* `TauCeti.IsEigenQuotient.linearMap_ext`: maps out of an eigenquotient agreeing after every `F i`
  are equal.
* `TauCeti.exists_isEigenQuotient`: existence of an eigenquotient.
* `TauCeti.IsEigenQuotient.continuous_apply`: the matrix coefficients of an eigenquotient of
  representations with continuous matrix coefficients are continuous.

## References

* The statements follow the definitions `New.Variety.IsEigenQuotient` and
  `New.Variety.exists_isEigenQuotient` in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open TensorProduct DirectSum

namespace TauCeti

universe u

variable {K : Type*} {L : Type u} {Γ ι S : Type*} {V : ι → Type*}

section Definitions

variable [CommSemiring K] [CommSemiring L] [Algebra K L] [Monoid Γ]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- A family of `K`-linear maps `G i : V i → W` into an `L`-linear representation `σ` of `Γ` is an
*eigenfamily* for the representations `ρ i`, the operators `T i s` and the eigenvalues `θ s` if
every `G i` is `Γ`-equivariant and `G i ∘ T i s = θ s • G i`. -/
@[mk_iff]
structure IsEigenFamily (ρ : ∀ i, Representation K Γ (V i)) (T : ∀ i, S → Module.End K (V i))
    (θ : S → L) {W : Type*} [AddCommMonoid W] [Module L W] [Module K W]
    (σ : Representation L Γ W) (G : ∀ i, V i →ₗ[K] W) : Prop where
  /-- Every map of the family is `Γ`-equivariant. -/
  map_apply (i : ι) (g : Γ) (x : V i) : G i (ρ i g x) = σ g (G i x)
  /-- The operator `T i s` acts through `G i` by the scalar `θ s`. -/
  map_eigen (i : ι) (s : S) (x : V i) : G i (T i s x) = θ s • G i x

/-- An *eigenquotient* of the representations `ρ i` for the operators `T i s` and the eigenvalues
`θ s` is an eigenfamily `F i : V i → L^N` into a representation `r` of `Γ` on `L^N` whose images
span `L^N` over `L`, and through which every eigenfamily `G` into an `L`-linear representation
factors uniquely: there is exactly one `L`-linear `φ : L^N → W` with `φ ∘ F i = G i` for every
`i`. The number `N` may be `0`. The universal property is asked for targets `W` in the universe
of `L`. -/
@[mk_iff]
structure IsEigenQuotient (ρ : ∀ i, Representation K Γ (V i))
    (T : ∀ i, S → Module.End K (V i)) (θ : S → L) {N : ℕ} (r : Representation L Γ (Fin N → L))
    (F : ∀ i, V i →ₗ[K] (Fin N → L)) : Prop extends IsEigenFamily ρ T θ r F where
  /-- The images of the maps `F i` span `L^N` over `L`. -/
  span_eq_top : Submodule.span L (⋃ i, Set.range (F i)) = ⊤
  /-- Every eigenfamily into an `L`-linear representation factors uniquely through the `F i`. -/
  existsUnique_comp (W : Type u) [AddCommMonoid W] [Module L W] [Module K W]
    [IsScalarTower K L W] (σ : Representation L Γ W) (G : ∀ i, V i →ₗ[K] W) :
    IsEigenFamily ρ T θ σ G →
      ∃! φ : (Fin N → L) →ₗ[L] W, ∀ i, φ.restrictScalars K ∘ₗ F i = G i

variable {ρ : ∀ i, Representation K Γ (V i)} {T : ∀ i, S → Module.End K (V i)} {θ : S → L}
  {N : ℕ} {r : Representation L Γ (Fin N → L)} {F : ∀ i, V i →ₗ[K] (Fin N → L)}

/-- Two `L`-linear maps out of an eigenquotient are equal if they agree after every `F i`. -/
theorem IsEigenQuotient.linearMap_ext {W : Type*} [AddCommMonoid W] [Module L W]
    (h : IsEigenQuotient ρ T θ r F) {φ ψ : (Fin N → L) →ₗ[L] W}
    (hφψ : ∀ i x, φ (F i x) = ψ (F i x)) : φ = ψ :=
  LinearMap.ext_on h.span_eq_top <| by
    simp only [Set.EqOn, Set.mem_iUnion, Set.mem_range]
    rintro _ ⟨i, x, rfl⟩
    exact hφψ i x

end Definitions

section Existence

variable [CommRing K] [Field L] [Algebra K L] [Monoid Γ]
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (ρ : ∀ i, Representation K Γ (V i)) (T : ∀ i, S → Module.End K (V i)) (θ : S → L)

variable [DecidableEq ι]

/-- The `K`-linear map `x ↦ 1 ⊗ x` from the summand `V i` into `L ⊗[K] ⨁ i, V i`. -/
private noncomputable def incl (i : ι) : V i →ₗ[K] L ⊗[K] ⨁ i, V i :=
  TensorProduct.mk K L (⨁ i, V i) 1 ∘ₗ lof K ι V i

private theorem baseChange_directSum_incl (g : Γ) (i : ι) (x : V i) :
    (Representation.directSum ρ).baseChange L g (incl i x) = incl i (ρ i g x) := by
  simp [incl]

/-- The `L`-span of the `Γ`-translates of the elements `1 ⊗ T i s x - θ s • (1 ⊗ x)`. -/
private noncomputable def rels : Submodule L (L ⊗[K] ⨁ i, V i) :=
  Submodule.span L {m | ∃ (g : Γ) (i : ι) (s : S) (x : V i),
    m = (Representation.directSum ρ).baseChange L g (incl i (T i s x) - θ s • incl i x)}

private theorem rels_le_comap (g : Γ) :
    rels ρ T θ ≤ (rels ρ T θ).comap ((Representation.directSum ρ).baseChange L g) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, i, s, x, rfl⟩
  refine Submodule.subset_span ⟨g * h, i, s, x, ?_⟩
  -- `(f * g) m = f (g m)` holds by definition in `Module.End`.
  rw [map_mul]
  rfl

/-- The elements `1 ⊗ x` span `L ⊗[K] ⨁ i, V i` over `L`. -/
private theorem span_range_incl :
    Submodule.span L (⋃ i, Set.range (incl (K := K) (L := L) (V := V) i)) = ⊤ := by
  have hK : Submodule.span K (⋃ i, Set.range (lof K ι V i)) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun y => ?_
    induction y using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of i x => exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, x, rfl⟩)
    | add y z hy hz => exact add_mem hy hz
  have himage : (⋃ i, Set.range (incl (K := K) (L := L) (V := V) i)) =
      TensorProduct.mk K L (⨁ i, V i) 1 '' ⋃ i, Set.range (lof K ι V i) := by
    simp only [Set.image_iUnion, ← Set.range_comp]
    rfl
  rw [himage, ← Submodule.baseChange_span, hK, Submodule.baseChange_top]

variable {ρ T θ}

/-- An eigenfamily `G` induces an `L`-linear map `L ⊗[K] ⨁ i, V i → W` killing `rels`. -/
private theorem rels_le_ker {W : Type*} [AddCommGroup W] [Module L W] [Module K W]
    [IsScalarTower K L W] {σ : Representation L Γ W} {G : ∀ i, V i →ₗ[K] W}
    (hG : IsEigenFamily ρ T θ σ G) :
    rels ρ T θ ≤ LinearMap.ker ((toModule K ι W G).liftBaseChange L) := by
  have hcomm : ∀ (g : Γ) (m : L ⊗[K] ⨁ i, V i), (toModule K ι W G).liftBaseChange L
      ((Representation.directSum ρ).baseChange L g m) =
        σ g ((toModule K ι W G).liftBaseChange L m) := by
    intro g m
    have hsum : toModule K ι W G ∘ₗ Representation.directSum ρ g =
        (σ g).restrictScalars K ∘ₗ toModule K ι W G := by
      ext i x
      simp [hG.map_apply]
    induction m using TensorProduct.inductionOn with
    | tmul a y =>
      rw [Representation.baseChange_apply, LinearMap.baseChange_tmul,
        LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      exact congrArg (a • ·) (LinearMap.congr_fun hsum y)
    | add m n hm hn => simp only [map_add, hm, hn]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, i, s, x, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, hcomm]
  simp [incl, hG.map_eigen]

variable (ρ T θ)

/-- The eigenquotient as a quotient of `L ⊗[K] ⨁ i, V i`. -/
private abbrev EigenQuot := (L ⊗[K] ⨁ i, V i) ⧸ rels ρ T θ

/-- The representation of `Γ` on `EigenQuot`. -/
private noncomputable abbrev quotRep : Representation L Γ (EigenQuot ρ T θ) :=
  ((Representation.directSum ρ).baseChange L).quotient (rels ρ T θ) (rels_le_comap ρ T θ)

/-- The universal maps into `EigenQuot`. -/
private noncomputable def quotMap (i : ι) : V i →ₗ[K] EigenQuot ρ T θ :=
  (rels ρ T θ).mkQ.restrictScalars K ∘ₗ incl i

private theorem isEigenFamily_quotMap : IsEigenFamily ρ T θ (quotRep ρ T θ) (quotMap ρ T θ) where
  map_apply i g x := by
    simp [quotMap, ← baseChange_directSum_incl]
  map_eigen i s x := by
    simp only [quotMap, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨1, i, s, x, ?_⟩
    -- `1 m = m` holds by definition in `Module.End`.
    rw [map_one]
    rfl

/-- Any eigenfamily factors through `quotMap`. -/
private theorem exists_comp_quotMap {W : Type*} [AddCommGroup W] [Module L W] [Module K W]
    [IsScalarTower K L W] {σ : Representation L Γ W} {G : ∀ i, V i →ₗ[K] W}
    (hG : IsEigenFamily ρ T θ σ G) :
    ∃ φ : EigenQuot ρ T θ →ₗ[L] W, ∀ i, φ.restrictScalars K ∘ₗ quotMap ρ T θ i = G i :=
  ⟨(rels ρ T θ).liftQ _ (rels_le_ker hG), fun i => by
    ext x
    simp [quotMap, incl]⟩

private theorem span_range_quotMap :
    Submodule.span L (⋃ i, Set.range (quotMap ρ T θ i)) = ⊤ := by
  have himage : (⋃ i, Set.range (quotMap ρ T θ i)) =
      (rels ρ T θ).mkQ '' ⋃ i, Set.range (incl (K := K) (L := L) (V := V) i) := by
    simp only [Set.image_iUnion, ← Set.range_comp]
    rfl
  rw [himage, Submodule.span_image, span_range_incl, Submodule.map_top, Submodule.range_mkQ]

end Existence

/-- **Existence of eigenquotients.** For a field extension `L` of the commutative ring `K` (any
`K`-algebra that is a field), finitely many representations `ρ i` of a monoid `Γ` on finite
`K`-modules `V i`, any operators `T i s` and any eigenvalues `θ s ∈ L`, an eigenquotient exists.
Its dimension `N` may be `0`. -/
theorem exists_isEigenQuotient [CommRing K] [Field L] [Algebra K L] [Monoid Γ] [Finite ι]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module.Finite K (V i)]
    (ρ : ∀ i, Representation K Γ (V i)) (T : ∀ i, S → Module.End K (V i)) (θ : S → L) :
    ∃ (N : ℕ) (r : Representation L Γ (Fin N → L)) (F : ∀ i, V i →ₗ[K] (Fin N → L)),
      IsEigenQuotient ρ T θ r F := by
  classical
  let e := (Module.finBasis L (EigenQuot ρ T θ)).equivFun
  let r : Representation L Γ (Fin _ → L) := e.conjRingEquiv.toMonoidHom.comp (quotRep ρ T θ)
  let F : ∀ i, V i →ₗ[K] (Fin _ → L) := fun i => e.toLinearMap.restrictScalars K ∘ₗ quotMap ρ T θ i
  have hF : IsEigenFamily ρ T θ r F :=
    { map_apply := fun i g x => by
        simp [r, F, (isEigenFamily_quotMap ρ T θ).map_apply]
      map_eigen := fun i s x => by
        simp [F, (isEigenFamily_quotMap ρ T θ).map_eigen] }
  have hspan : Submodule.span L (⋃ i, Set.range (F i)) = ⊤ := by
    have : (⋃ i, Set.range (F i)) = e '' ⋃ i, Set.range (quotMap ρ T θ i) := by
      simp only [Set.image_iUnion, ← Set.range_comp]
      rfl
    rw [this, ← LinearEquiv.coe_toLinearMap, Submodule.span_image, span_range_quotMap,
      Submodule.map_top, LinearEquiv.range]
  refine ⟨_, r, F, { hF with span_eq_top := hspan, existsUnique_comp := ?_ }⟩
  intro W _ _ _ _ σ G hG
  let := Module.addCommMonoidToAddCommGroup L (M := W)
  obtain ⟨φ, hφ⟩ := exists_comp_quotMap ρ T θ hG
  refine ⟨φ ∘ₗ e.symm.toLinearMap, fun i => ?_, fun ψ hψ => ?_⟩
  · ext x
    simpa [F] using LinearMap.congr_fun (hφ i) x
  · refine LinearMap.ext_on hspan ?_
    simp only [Set.EqOn, Set.mem_iUnion, Set.mem_range]
    rintro _ ⟨i, x, rfl⟩
    have h1 : ψ (e (quotMap ρ T θ i x)) = G i x := LinearMap.congr_fun (hψ i) x
    have h2 : φ (quotMap ρ T θ i x) = G i x := LinearMap.congr_fun (hφ i) x
    simp [F, h1, h2]

section Continuity

variable [CommSemiring K] [CommSemiring L] [Algebra K L] [Monoid Γ]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
  [TopologicalSpace Γ] [TopologicalSpace K] [TopologicalSpace L]

/-- A `K`-linear map `μ : V → L` composed with an orbit of a representation with continuous matrix
coefficients on a finite free module is continuous. -/
private theorem continuous_linearMap_apply [ContinuousAdd L] [ContinuousSMul K L]
    {W : Type*} [AddCommMonoid W] [Module K W] [Module.Free K W] [Module.Finite K W]
    {π : Representation K Γ W} (hπ : ∀ (f : Module.Dual K W) (x : W), Continuous fun g => f (π g x))
    (μ : W →ₗ[K] L) (x : W) : Continuous fun g => μ (π g x) := by
  let b := Module.Free.chooseBasis K W
  have h : ∀ g, μ (π g x) = ∑ j, b.coord j (π g x) • μ (b j) := fun g => calc
    μ (π g x) = μ (∑ j, b.repr (π g x) j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.coord j (π g x) • μ (b j) := by
      simp only [map_sum, map_smul, Module.Basis.coord_apply]
  simp only [h]
  exact continuous_finsetSum _ fun j _ => (hπ (b.coord j) x).smul continuous_const

/-- **Continuity of eigenquotients.** If every `V i` is finite free over `K` and every matrix
coefficient `g ↦ f (ρ i g x)` is continuous, then every matrix coefficient `g ↦ l (r g y)` of an
eigenquotient `r` is continuous. -/
theorem IsEigenQuotient.continuous_apply [ContinuousAdd L] [ContinuousSMul K L]
    [∀ i, Module.Free K (V i)] [∀ i, Module.Finite K (V i)]
    {ρ : ∀ i, Representation K Γ (V i)} {T : ∀ i, S → Module.End K (V i)} {θ : S → L} {N : ℕ}
    {r : Representation L Γ (Fin N → L)} {F : ∀ i, V i →ₗ[K] (Fin N → L)}
    (h : IsEigenQuotient ρ T θ r F)
    (hρ : ∀ i (f : Module.Dual K (V i)) (x : V i), Continuous fun g => f (ρ i g x))
    (l : (Fin N → L) →ₗ[L] L) (y : Fin N → L) : Continuous fun g => l (r g y) := by
  have hy : y ∈ Submodule.span L (⋃ i, Set.range (F i)) := h.span_eq_top ▸ Submodule.mem_top
  induction hy using Submodule.span_induction generalizing l with
  | mem y hy =>
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    simp only [← h.map_apply]
    exact continuous_linearMap_apply (hρ i) (l.restrictScalars K ∘ₗ F i) x
  | zero => simpa using continuous_const
  | add y z _ _ hy hz =>
    simp only [map_add]
    exact (hy l).add (hz l)
  | smul c y _ hy =>
    -- The scalar `c` is absorbed into the linear form: `l (c • v) = (c • l) v`.
    simpa only [map_smul, LinearMap.smul_apply] using hy (c • l)

end Continuity

end TauCeti
