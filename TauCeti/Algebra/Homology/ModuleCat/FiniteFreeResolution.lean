/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Finite free resolutions of complexes with finitely generated homology

Let `R` be a (left) Noetherian ring. A complex of `R`-modules whose homology is finitely
generated in every degree, and vanishes in high cohomological degrees, receives a
quasi-isomorphism from a complex of finitely generated free `R`-modules with the same bound:

* `ChainComplex.exists_quasiIso_finite_free`: every chain complex `K` of `R`-modules indexed by
  `ℕ` with finitely generated homology admits a quasi-isomorphism `L ⟶ K` from a chain complex `L`
  of finitely generated free modules;
* `CochainComplex.exists_quasiIso_finite_free`: every cochain complex `K` of `R`-modules indexed
  by `ℤ` with finitely generated cohomology and `Hⁱ(K) = 0` for `i > n` admits a
  quasi-isomorphism `L ⟶ K` from a cochain complex `L` of finitely generated free modules with
  `Lⁱ = 0` for `i > n`.

The terms of `K` themselves need not be finitely generated. This is the first step of the lemma
of Mumford and Grothendieck on cohomology and base change: for a proper morphism `X ⟶ Spec R` and
a coherent sheaf on `X` flat over `R`, the Čech complex of the sheaf has finitely generated
cohomology and flat terms, and it is replaced by such a complex `L` of finite free modules.

The chain complex `L` is built one degree at a time, as in Hartshorne's proof. Suppose that
`L₀, …, L_k` and the components `g_i : L_i → K_i` of the chain map are constructed, with
`H_i(g)` bijective for `i < k`, and every cycle of `K_k` the sum of a boundary and the image of
an element of the submodule `Z ⊆ L_k` of cycles of `L`. Choose finitely many generators of the
submodule of those `z ∈ Z` with `g_k z` a boundary of `K`, which is finitely generated because
`R` is Noetherian, together with elements of `K_{k+1}` whose boundaries are their images, and
finitely many cycles of `K_{k+1}` representing generators of `H_{k+1}(K)`. The free module
`L_{k+1}` on these generators, with the evident maps to `L_k` and `K_{k+1}`, makes `H_k(g)`
injective, and every cycle of `K_{k+1}` the sum of a boundary and the image of a cycle of
`L_{k+1}`, so that `H_{k+1}(g)` will be surjective onto `H_{k+1}(K)`. The cochain complex
version follows by applying the chain complex version to the canonical truncation of `K` in
degrees `≤ n`, reindexed by `ℕ`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Lemma III.12.3.
* D. Mumford, *Abelian Varieties*, Tata Institute, 1970, §5, the lemma on cohomology and base
  change.
-/

public section

open CategoryTheory Limits

universe u

namespace ChainComplex

variable {R : Type u} [Ring R]

namespace FiniteFreeResolution

variable (K : ChainComplex (ModuleCat.{u} R) ℕ)

/-- A finite free resolution of `K` constructed up to degree `k`: the free module `L_k` on the
finite type `ι`, the degree-`k` component `g` of the chain map, and the submodule `Z` of cycles of
`L_k`, such that every cycle of `K_k` is the image of a cycle in `Z` up to a boundary. -/
private structure Stage (k : ℕ) where
  /-- The index type of the basis of `L_k`. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The degree-`k` component of the chain map. -/
  g : (ι → R) →ₗ[R] K.X k
  /-- The cycles of `L_k`. -/
  Z : Submodule R (ι → R)
  surj : ∀ x : K.X k, (∀ l, K.d k l x = 0) →
    ∃ z ∈ Z, ∃ y : K.X (k + 1), g z + K.d (k + 1) k y = x

attribute [instance] Stage.fintype

variable {K}

/-- The next degree `L_{k+1}` of a finite free resolution: the differential `δ` to `L_k` and the
component `g` of the chain map, compatible with each other, such that the boundaries of `L_k`
are the cycles of `Z` sent to boundaries, and every cycle of `K_{k+1}` comes from a cycle of
`L_{k+1}` up to a boundary. -/
private structure Stage.Extension {k : ℕ} (S : Stage K k) where
  /-- The index type of the basis of `L_{k+1}`. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The differential `L_{k+1} → L_k`. -/
  δ : (ι → R) →ₗ[R] (S.ι → R)
  /-- The degree-`(k + 1)` component of the chain map. -/
  g : (ι → R) →ₗ[R] K.X (k + 1)
  range_le : LinearMap.range δ ≤ S.Z
  comm : ∀ v, K.d (k + 1) k (g v) = S.g (δ v)
  mem_range : ∀ z ∈ S.Z, ∀ y : K.X (k + 1), K.d (k + 1) k y = S.g z → z ∈ LinearMap.range δ
  surj : ∀ x : K.X (k + 1), K.d (k + 1) k x = 0 →
    ∃ z ∈ LinearMap.ker δ, ∃ y : K.X (k + 1 + 1), g z + K.d (k + 1 + 1) (k + 1) y = x

attribute [instance] Stage.Extension.fintype

/-- The stage in degree `k + 1` given by an extension. -/
private def Stage.Extension.toStage {k : ℕ} {S : Stage K k} (E : S.Extension) :
    Stage K (k + 1) where
  ι := E.ι
  g := E.g
  Z := LinearMap.ker E.δ
  surj x hx := E.surj x (hx k)

/-- Over a Noetherian ring, a stage extends to the next degree when the homology of `K` there is
finitely generated. -/
private lemma Stage.nonempty_extension [IsNoetherianRing R] {k : ℕ} (S : Stage K k)
    (hK : Module.Finite R (K.homology (k + 1))) : Nonempty S.Extension := by
  classical
  -- the cycles of `L_k` sent to boundaries of `K`
  let N : Submodule R (S.ι → R) := S.Z ⊓ (LinearMap.range (K.d (k + 1) k).hom).comap S.g
  obtain ⟨m₁, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian N)
  have hvN (i : Fin m₁) : v i ∈ N := hv ▸ Submodule.subset_span ⟨i, rfl⟩
  choose y hy using fun i ↦ (hvN i).2
  obtain ⟨m₂, c, hc, hcgen⟩ :=
    K.exists_fin_moduleCat_cycles_generating hK (ChainComplex.prev ℕ (k + 1))
  refine ⟨{ ι := Fin m₁ ⊕ Fin m₂
            δ := Fintype.linearCombination R (Sum.elim v 0)
            g := Fintype.linearCombination R (Sum.elim y c)
            range_le := ?_
            comm := fun a ↦ ?_
            mem_range := fun z hz y' hy' ↦ ?_
            surj := fun x hx ↦ ?_ }⟩
  · rw [Fintype.range_linearCombination, Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact (hvN i).1
    · exact S.Z.zero_mem
  · simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum, map_smul, hc,
      ← hy]
  · have hz' : z ∈ Submodule.span R (Set.range v) := hv ▸ ⟨hz, y', hy'⟩
    rw [Fintype.range_linearCombination]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩) hz'
  · obtain ⟨r, y', hy'⟩ := hcgen x (K.d_apply_eq_zero_of_d_next_apply_eq_zero (by simp) hx)
    refine ⟨Sum.elim 0 r, ?_, y', ?_⟩
    · simp [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    · simpa [Fintype.linearCombination_apply, Fintype.sum_sum_type] using hy'

/-- A choice of extension of a stage. -/
private noncomputable def Stage.extension [IsNoetherianRing R] {k : ℕ} (S : Stage K k)
    (hK : Module.Finite R (K.homology (k + 1))) : S.Extension :=
  Classical.choice (S.nonempty_extension hK)

variable (K)

/-- The stage in degree zero: the free module on finitely many cycles representing generators of
`H₀(K)`, all of whose elements are cycles. -/
private noncomputable def stageZero (hK : Module.Finite R (K.homology 0)) : Stage K 0 where
  ι := Fin (K.exists_fin_moduleCat_cycles_generating hK (ChainComplex.prev ℕ 0)).choose
  g := Fintype.linearCombination R
    (K.exists_fin_moduleCat_cycles_generating hK (ChainComplex.prev ℕ 0)).choose_spec.choose
  Z := ⊤
  surj x hx := by
    obtain ⟨r, y, hy⟩ := (K.exists_fin_moduleCat_cycles_generating hK
      (ChainComplex.prev ℕ 0)).choose_spec.choose_spec.2 x hx
    exact ⟨r, Submodule.mem_top, y, by rwa [Fintype.linearCombination_apply]⟩

variable [IsNoetherianRing R] (hK : ∀ k, Module.Finite R (K.homology k))

/-- The stages of the finite free resolution in all degrees. -/
private noncomputable def stage : (k : ℕ) → Stage K k
  | 0 => stageZero K (hK 0)
  | k + 1 => ((stage k).extension (hK (k + 1))).toStage

/-- Every element of the free module in degree zero is a cycle. -/
private lemma stage_zero_Z : (stage K hK 0).Z = ⊤ := rfl

/-- The stage in degree `k + 1` is, by definition, the stage of the chosen extension of the stage
in degree `k`: its basis is the extension's basis, so `L_{k+1}` is the free module on it, and its
chain map component is that of the extension. -/
private lemma stage_succ_g (k : ℕ) :
    (stage K hK (k + 1)).g = ((stage K hK k).extension (hK (k + 1))).g := rfl

/-- The cycles of `L_{k+1}` are the kernel of the extension's differential to `L_k`. -/
private lemma stage_succ_Z (k : ℕ) :
    (stage K hK (k + 1)).Z = LinearMap.ker ((stage K hK k).extension (hK (k + 1))).δ := rfl

/-- The finite free resolution of `K`. It is reducible so that its terms are seen to be the free
modules `ι → R` of the stages. -/
private noncomputable abbrev resolution : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun k ↦ ModuleCat.of R ((stage K hK k).ι → R))
    (fun k ↦ ModuleCat.ofHom ((stage K hK k).extension (hK (k + 1))).δ)
    (fun k ↦ ModuleCat.hom_ext <| LinearMap.ext fun z ↦ LinearMap.mem_ker.1 <|
      ((stage K hK (k + 1)).extension (hK (k + 1 + 1))).range_le ⟨z, rfl⟩)

private lemma resolution_d_apply (k : ℕ) (z : (resolution K hK).X (k + 1)) :
    (resolution K hK).d (k + 1) k z = ((stage K hK k).extension (hK (k + 1))).δ z := by
  simp only [resolution, ChainComplex.of_d]
  exact ModuleCat.ofHom_apply _ z

/-- The quasi-isomorphism from the finite free resolution to `K`. -/
private noncomputable def toComplex : resolution K hK ⟶ K where
  f k := ModuleCat.ofHom (stage K hK k).g
  comm' := by
    rintro _ k rfl
    ext z
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [stage_succ_g, resolution_d_apply]
    exact ((stage K hK k).extension (hK (k + 1))).comm z

/-- The submodule `Z` of a stage consists of the cycles of the resolution. -/
private lemma mem_Z_iff (k : ℕ) (z : (stage K hK k).ι → R) :
    z ∈ (stage K hK k).Z ↔ (resolution K hK).d k ((ComplexShape.down ℕ).next k) z = 0 := by
  cases k with
  | zero =>
    rw [stage_zero_Z, (resolution K hK).shape 0 _ (by simp)]
    simp
  | succ k =>
    have h : (ComplexShape.down ℕ).next (k + 1) = k := by simp
    rw [stage_succ_Z, h, resolution_d_apply]
    exact LinearMap.mem_ker (f := ((stage K hK k).extension (hK (k + 1))).δ)

private lemma quasiIsoAt_toComplex (k : ℕ) : QuasiIsoAt (toComplex K hK) k := by
  set L := resolution K hK
  set φ := toComplex K hK
  set E := (stage K hK k).extension (hK (k + 1))
  set m := (ComplexShape.down ℕ).next k
  have hm : (ComplexShape.down ℕ).next k = m := rfl
  have hp : (ComplexShape.down ℕ).prev k = k + 1 := ChainComplex.prev ℕ k
  -- homology classes of cycles, as elements of the kernels of the differentials
  let cL := L.moduleCatHomologyClass hm (LinearMap.ker (L.d k m).hom).subtype
    fun z ↦ LinearMap.mem_ker.1 z.2
  let cK := K.moduleCatHomologyClass hm (LinearMap.ker (K.d k m).hom).subtype
    fun z ↦ LinearMap.mem_ker.1 z.2
  let φZ := (φ.f k).hom.restrict fun x (hx : x ∈ LinearMap.ker (L.d k m).hom) ↦
    LinearMap.mem_ker.2 (φ.d_apply_eq_zero_of_d_apply_eq_zero k m x hx)
  have hnat (z) : HomologicalComplex.homologyMap φ k (cL z) = cK (φZ z) :=
    HomologicalComplex.homologyMap_moduleCatHomologyClass hm _ _ φ _ _ φZ (fun _ ↦ rfl) z
  have hLsurj : Function.Surjective cL :=
    L.moduleCatHomologyClass_surjective hm _ _ fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  have hKsurj : Function.Surjective cK :=
    K.moduleCatHomologyClass_surjective hm _ _ fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero (HomologicalComplex.homologyMap φ k).hom).2 fun h hh ↦ ?_,
    fun h ↦ ?_⟩
  · -- a cycle `z` of `L` whose image is a boundary of `K` is a boundary of `L`
    obtain ⟨z, rfl⟩ := hLsurj h
    obtain ⟨y, hy⟩ := (K.moduleCatHomologyClass_eq_zero_iff hm _ _ hp _).1 ((hnat z).symm.trans hh)
    obtain ⟨w, hw⟩ := E.mem_range z.1 ((mem_Z_iff K hK k z.1).2 z.2) y hy
    -- `w` lies in `L.X (k + 1)`, the free module on the basis `E.ι` of `stage K hK (k + 1)`
    exact (L.moduleCatHomologyClass_eq_zero_iff hm _ _ hp _).2
      ⟨w, (resolution_d_apply K hK k w).trans hw⟩
  · -- a cycle `x` of `K` is the image of a cycle `z` of `L` up to a boundary
    obtain ⟨⟨x, hx⟩, rfl⟩ := hKsurj h
    have hx' : ∀ l, K.d k l x = 0 :=
      K.d_apply_eq_zero_of_d_next_apply_eq_zero hm (LinearMap.mem_ker.1 hx)
    obtain ⟨z, hz, y, hy⟩ := (stage K hK k).surj x hx'
    refine ⟨cL ⟨z, (mem_Z_iff K hK k z).1 hz⟩, ?_⟩
    rw [hnat, eq_comm, ← sub_eq_zero, ← map_sub]
    exact (K.moduleCatHomologyClass_eq_zero_iff hm _ _ hp _).2 ⟨y, eq_sub_of_add_eq' hy⟩

end FiniteFreeResolution

open FiniteFreeResolution in
/-- Over a Noetherian ring, every chain complex of modules indexed by `ℕ` whose homology is
finitely generated in every degree receives a quasi-isomorphism from a chain complex of finitely
generated free modules. -/
theorem exists_quasiIso_finite_free [IsNoetherianRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ k, Module.Finite R (K.homology k)) :
    ∃ (L : ChainComplex (ModuleCat.{u} R) ℕ) (φ : L ⟶ K), QuasiIso φ ∧
      ∀ k, Module.Free R (L.X k) ∧ Module.Finite R (L.X k) := by
  refine ⟨resolution K hK, toComplex K hK, ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · rw [quasiIso_iff]
    exact quasiIsoAt_toComplex K hK
  · exact inferInstanceAs (Module.Free R ((stage K hK k).ι → R))
  · exact inferInstanceAs (Module.Finite R ((stage K hK k).ι → R))

end ChainComplex

namespace CochainComplex

open HomologicalComplex

variable {R : Type u} [Ring R]

/-- Over a Noetherian ring, every cochain complex `K` of modules indexed by `ℤ` whose cohomology
is finitely generated in every degree and vanishes in degrees `> n` receives a quasi-isomorphism
from a cochain complex of finitely generated free modules that vanishes in degrees `> n`. -/
theorem exists_quasiIso_finite_free [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) [K.IsLE n] (hK : ∀ i, Module.Finite R (K.homology i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ) (φ : L ⟶ K), L.IsStrictlyLE n ∧ QuasiIso φ ∧
      ∀ i, Module.Free R (L.X i) ∧ Module.Finite R (L.X i) := by
  set e := ComplexShape.embeddingUpIntLE n
  -- the homology of the canonical truncation `τ≤n K`, reindexed by `ℕ`, is that of `K`
  have hK' (k : ℕ) : Module.Finite R ((K.truncLE' e).homology k) :=
    Module.Finite.equiv (((K.truncLE' e).extendHomologyIso e rfl).symm ≪≫
      homologyMapIso (K.truncLEIso e).symm _ ≪≫
      asIso (homologyMap (HomologicalComplex.ιTruncLE K e) (e.f k))).toLinearEquiv.symm
  obtain ⟨L, ψ, hψ, hL⟩ := ChainComplex.exists_quasiIso_finite_free _ hK'
  have : QuasiIso (HomologicalComplex.ιTruncLE K e) :=
    (quasiIso_ιTruncLE_iff_isSupported K e).2 inferInstance
  refine ⟨L.extend e,
    extendMap ψ e ≫ (K.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE K e,
    inferInstance, inferInstance, fun i ↦ ?_⟩
  by_cases hi : ∃ k, e.f k = i
  · obtain ⟨k, hk⟩ := hi
    obtain ⟨_, _⟩ := hL k
    let f := (L.extendXIso e hk).toLinearEquiv
    exact ⟨Module.Free.of_equiv f.symm, Module.Finite.equiv f.symm⟩
  · have := ModuleCat.subsingleton_of_isZero (L.isZero_extend_X e i (by simpa using hi))
    exact ⟨inferInstance, inferInstance⟩

end CochainComplex
