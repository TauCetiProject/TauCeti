/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.Module.Equiv.Basic

/-!
# Dimensions of submodules

Dimension-counting criteria for nontrivial submodule intersection: two subspaces of a
finite-dimensional space whose dimensions sum to more than the ambient dimension meet
nontrivially, as do three subspaces whose dimensions sum to more than twice the ambient dimension,
and a subspace of rank greater than the rank of a linear map `f` meets `ker f`
nontrivially. Dually, the preimage of a subspace `W` under a linear map out of an
`m`-dimensional space has codimension at most the codimension of `W`. A set spans a subspace of
dimension at least `n` exactly when it contains `n` linearly independent vectors, and a subspace
of rank at least `k` contains a subspace of rank exactly `k`. Two disjoint subspaces of a
finite-dimensional subspace `U` have dimensions adding to at most that of `U`.
A subspace of dimension at least three contains `x` outside `𝕜 ∙ a` and `z` outside
`span 𝕜 {a, x}`.
A finite-dimensional subspace spanning the whole space together with `V`, of dimension at most the
codimension of `V`, is a complement of `V`; here `V` itself may be infinite-dimensional.

The rank of a product `V.prod W` of free submodules is the sum of their ranks over any
semiring satisfying the strong rank condition. Consequently, the rank of a product map
`f.prodMap g` with free ranges is the sum of the ranks of `f` and `g`. The dimension of the range
of a linear map is unchanged by composing on the left with an injective map and on the right with a
surjective one, and composing on the left with a map that does not lower the dimension of the range
does not enlarge the kernel. Conjugating an endomorphism by a linear equivalence preserves the
dimension of its kernel.
The kernel of a surjection from a finite-dimensional space has dimension the difference of the
dimensions.
-/

public section

open Module (finrank)

universe u v

namespace Submodule

variable {𝕜 : Type*}

section DivisionRing

variable [DivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Intersecting with a fixed subspace gives a supermodular dimension function. -/
theorem finrank_inf_add_finrank_inf_le (U V H : Submodule 𝕜 E) [FiniteDimensional 𝕜 H] :
    finrank 𝕜 ↥(U ⊓ H) + finrank 𝕜 ↥(V ⊓ H) ≤
      finrank 𝕜 ↥((U ⊓ V) ⊓ H) + finrank 𝕜 ↥((U ⊔ V) ⊓ H) := by
  have hdim := finrank_sup_add_finrank_inf_eq (U ⊓ H) (V ⊓ H)
  have hsub : (U ⊓ H) ⊔ (V ⊓ H) ≤ (U ⊔ V) ⊓ H :=
    sup_le (inf_le_inf_right H le_sup_left) (inf_le_inf_right H le_sup_right)
  have hle := finrank_mono hsub
  have hinf : (U ⊓ H) ⊓ (V ⊓ H) = (U ⊓ V) ⊓ H := by
    simp only [inf_assoc, inf_left_comm, inf_idem]
  rw [hinf] at hdim
  omega

/-- Two subspaces whose dimensions sum to more than the dimension of the ambient
space have nontrivial intersection. -/
theorem inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {V W : Submodule 𝕜 E}
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : V ⊓ W ≠ ⊥ := fun hbot =>
  absurd (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot))
    (by omega)

/-
Call sites supply `E` explicitly. Leaving it to unification makes the elaborator look for an
`AddCommGroup` structure on a space -- of linear maps, of tensors -- whose `AddCommMonoid`
structure is already fixed, which it does not find quickly.
-/

/-- Two disjoint subspaces of a finite-dimensional subspace `U` have dimensions adding to at most
that of `U`. This is the relative form of `Submodule.finrank_add_finrank_le_of_disjoint`, which
bounds them by the dimension of the ambient space. -/
theorem finrank_add_finrank_le_of_disjoint_of_le {S T U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    (h : Disjoint S T) (hS : S ≤ U) (hT : T ≤ U) :
    finrank 𝕜 S + finrank 𝕜 T ≤ finrank 𝕜 U := by
  have := finiteDimensional_of_le hS
  have := finiteDimensional_of_le hT
  rw [← finrank_sup_add_finrank_inf_eq, h.eq_bot, finrank_bot, add_zero]
  exact finrank_mono (sup_le hS hT)

/-- Three subspaces whose dimensions sum to more than twice the dimension of the ambient
space have nontrivial common intersection. -/
theorem inf_inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {U V W : Submodule 𝕜 E}
    (h : 2 * finrank 𝕜 E < finrank 𝕜 U + finrank 𝕜 V + finrank 𝕜 W) : U ⊓ V ⊓ W ≠ ⊥ := by
  have hUV := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hle := (U ⊔ V).finrank_le
  exact inf_ne_bot_of_finrank_lt (by omega)

/-- The preimage of a subspace `W` under a linear map `f : M → N` of finite-dimensional spaces
has codimension at most the codimension of `W`: `dim M + dim W ≤ dim (f⁻¹ W) + dim N`. -/
theorem finrank_add_finrank_le_finrank_comap_add_finrank {M N : Type*} [AddCommGroup M]
    [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (f : M →ₗ[𝕜] N) (W : Submodule 𝕜 N) :
    finrank 𝕜 M + finrank 𝕜 W ≤ finrank 𝕜 (W.comap f) + finrank 𝕜 N := by
  -- The preimage is the kernel of `M → N ⧸ W`; apply rank–nullity to that map.
  have hker : LinearMap.ker (W.mkQ ∘ₗ f) = W.comap f := by
    rw [LinearMap.ker_comp, ker_mkQ]
  have h₁ := LinearMap.finrank_range_add_finrank_ker (W.mkQ ∘ₗ f)
  have h₂ := (W.mkQ ∘ₗ f).range.finrank_le
  have h₃ := W.finrank_quotient_add_finrank
  rw [hker] at h₁
  omega

/-- A set spans a subspace of dimension at least `n` exactly when it contains `n` linearly
independent vectors. -/
theorem le_finrank_span_iff_exists_linearIndependent {s : Set E} [Module.Finite 𝕜 (span 𝕜 s)]
    {n : ℕ} :
    n ≤ finrank 𝕜 (span 𝕜 s) ↔ ∃ v : Fin n → E, LinearIndependent 𝕜 v ∧ ∀ i, v i ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv, hvs⟩ ↦ ?_⟩
  · obtain ⟨f, hfs, -, hf⟩ := exists_fun_fin_finrank_span_eq 𝕜 s
    exact ⟨f ∘ Fin.castLE h, hf.comp _ (Fin.castLE_injective h), fun i ↦ hfs _⟩
  · have := finrank_mono (span_mono (R := 𝕜) (Set.range_subset_iff.2 hvs))
    rwa [finrank_span_eq_card hv, Fintype.card_fin] at this

/-- A finite-dimensional subspace `S` which spans the whole space together with `V`, and whose
dimension is at most the codimension of `V`, is a complement of `V`. Indeed `S` maps onto
`E ⧸ V`, so the two dimensions agree and the map is injective. -/
theorem isCompl_of_codisjoint_of_finrank_le {V S : Submodule 𝕜 E} [FiniteDimensional 𝕜 S]
    (h : Codisjoint V S) (hrank : finrank 𝕜 S ≤ finrank 𝕜 (E ⧸ V)) : IsCompl V S := by
  let φ : S →ₗ[𝕜] E ⧸ V := V.mkQ ∘ₗ S.subtype
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, range_subtype, map_mkQ_eq_top]
    exact h.eq_top
  have : FiniteDimensional 𝕜 (E ⧸ V) := Module.Finite.of_surjective φ hφ
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hrank.antisymm (LinearMap.finrank_le_finrank_of_surjective hφ))).mpr hφ
  refine ⟨disjoint_def.mpr fun x hxV hxS ↦ ?_, h⟩
  have : φ ⟨x, hxS⟩ = φ 0 := by simpa [φ] using hxV
  simpa using congrArg Subtype.val (hinj this)

/-- A subspace of rank at least `k` contains a subspace of rank exactly `k`: the span of `k`
linearly independent vectors of it. The rank of `M` may be an infinite cardinal. -/
theorem exists_le_rank_eq {M : Submodule 𝕜 E} {k : ℕ} (hk : (k : Cardinal) ≤ Module.rank 𝕜 M) :
    ∃ N ≤ M, Module.rank 𝕜 N = k := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hk
  have hv' : LinearIndependent 𝕜 (M.subtype ∘ v) := hv.map' M.subtype M.ker_subtype
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range (M.subtype ∘ v))
  refine ⟨span 𝕜 (Set.range (M.subtype ∘ v)),
    span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (v i).2), ?_⟩
  rw [← Module.finrank_eq_rank, finrank_span_eq_card hv', Fintype.card_fin]

/-- The linear-algebra core of the transverse level disc, kernel part. If `T` has dimension
`dim G + 1`, `T` and the kernel of a surjection `π` span the space, and some `v ∈ T` with
`dg v ≠ 0` for a linear form `dg` lies in the kernel of `π`, then `T ⊓ ker dg` meets `ker π`
trivially, that is, `π` is injective on `T ⊓ ker dg`. -/
theorem disjoint_inf_ker_ker_of_finrank_eq_succ {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    {T : Submodule 𝕜 E} {π : E →ₗ[𝕜] G} {dg : E →ₗ[𝕜] 𝕜} {v : E}
    (hπs : Function.Surjective π) (hTπ : T ⊔ LinearMap.ker π = ⊤)
    (hdim : Module.finrank 𝕜 T = Module.finrank 𝕜 G + 1) (hvs : v ∈ T) (hvπ : π v = 0)
    (hgv : dg v ≠ 0) :
    Disjoint (T ⊓ LinearMap.ker dg) (LinearMap.ker π) := by
  have : FiniteDimensional 𝕜 T := Module.finite_of_finrank_eq_succ hdim
  have hv0 : v ≠ 0 := by rintro rfl; exact hgv (map_zero _)
  have hsurj : Function.Surjective (π.domRestrict T) :=
    (LinearMap.surjective_domRestrict_iff hπs).2 (codisjoint_iff.2 hTπ)
  have : FiniteDimensional 𝕜 G := Module.Finite.of_surjective _ hsurj
  have hker : LinearMap.ker (π.domRestrict T) = (T ⊓ LinearMap.ker π).comap T.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have hkerπ := LinearMap.finrank_range_add_finrank_ker (π.domRestrict T)
  rw [LinearMap.range_eq_top_of_surjective _ hsurj, finrank_top, hker,
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hkerπ
  have hline : T ⊓ LinearMap.ker π = 𝕜 ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one (by omega) ⟨hvs, hvπ⟩ hv0
  rw [disjoint_iff, inf_right_comm, hline]
  exact (Submodule.disjoint_span_singleton_of_notMem
    (s := LinearMap.ker dg) fun h ↦ hgv (LinearMap.mem_ker.1 h)).symm.eq_bot

/-- A subspace with more dimensions than a finite set has elements contains a vector outside the
span of the set. -/
theorem exists_mem_notMem_span_of_ncard_lt {V : Submodule 𝕜 E} {s : Set E} (hs : s.Finite)
    (h : s.ncard < finrank 𝕜 V) : ∃ z ∈ V, z ∉ span 𝕜 s := by
  by_contra! hz
  have : Module.Finite 𝕜 V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional 𝕜 (span 𝕜 s) := FiniteDimensional.span_of_finite 𝕜 hs
  have h1 := Submodule.finrank_mono (fun u hu ↦ hz u hu : V ≤ span 𝕜 s)
  have h2 := finrank_span_le_ncard (R := 𝕜) s hs
  omega

/-- A subspace of dimension at least three contains a vector `x` outside `𝕜 ∙ a` and a vector `z`
outside `span {a, x}`. -/
theorem exists_mem_notMem_span_pair {V : Submodule 𝕜 E} (a : E) (h : 3 ≤ finrank 𝕜 V) :
    ∃ x ∈ V, x ∉ 𝕜 ∙ a ∧ ∃ z ∈ V, z ∉ span 𝕜 {a, x} := by
  obtain ⟨x, hxV, hxa⟩ := exists_mem_notMem_span_of_ncard_lt (V := V) (Set.finite_singleton a)
    (by rw [Set.ncard_singleton]; omega)
  refine ⟨x, hxV, hxa, exists_mem_notMem_span_of_ncard_lt (Set.toFinite _) ?_⟩
  have := Set.ncard_insert_le a ({x} : Set E)
  rw [Set.ncard_singleton] at this
  omega

end DivisionRing

/-- A submodule meeting the kernel of `f` trivially has rank at most the rank of `f`, since `f`
maps it injectively into its range. -/
theorem lift_rank_le_of_disjoint_ker [Ring 𝕜] {M : Type u} {N : Type v}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    {V : Submodule 𝕜 M} {f : M →ₗ[𝕜] N} (h : Disjoint V (LinearMap.ker f)) :
    Cardinal.lift.{v} (Module.rank 𝕜 V) ≤ Cardinal.lift.{u} f.rank := by
  apply (f.rangeRestrict.domRestrict V).lift_rank_le_of_injective
  simpa only [LinearMap.injective_domRestrict_iff, LinearMap.ker_rangeRestrict] using h

/-- The rank of a product of free submodules is the sum of their ranks. -/
theorem rank_prod [Semiring 𝕜] [StrongRankCondition 𝕜] {M : Type u} {N : Type v}
    [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
    (V : Submodule 𝕜 M) (W : Submodule 𝕜 N) [Module.Free 𝕜 V] [Module.Free 𝕜 W] :
    Module.rank 𝕜 (V.prod W) =
      Cardinal.lift.{v} (Module.rank 𝕜 V) + Cardinal.lift.{u} (Module.rank 𝕜 W) := by
  rw [(V.prodEquiv W).rank_eq, _root_.rank_prod]

end Submodule

namespace LinearMap

variable {𝕜 M N : Type*} {M' : Type u} {N' : Type v} [Semiring 𝕜] [StrongRankCondition 𝕜]
  [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
  [AddCommMonoid M'] [Module 𝕜 M'] [AddCommMonoid N'] [Module 𝕜 N']

/-- The rank of a product map with free ranges is the sum of the ranks of its components. -/
theorem rank_prodMap (f : M →ₗ[𝕜] M') (g : N →ₗ[𝕜] N')
    [Module.Free 𝕜 f.range] [Module.Free 𝕜 g.range] :
    (f.prodMap g).rank = Cardinal.lift.{v} f.rank + Cardinal.lift.{u} g.rank := by
  rw [LinearMap.rank, range_prodMap, Submodule.rank_prod]

omit [StrongRankCondition 𝕜] in
/-- The dimension of the range of a linear map is unchanged by composing on the left with an
injective map and on the right with a surjective one. -/
theorem finrank_range_comp_comp {V : Type*} [AddCommMonoid V] [Module 𝕜 V] (A : N →ₗ[𝕜] N')
    (L : M →ₗ[𝕜] N) (B : V →ₗ[𝕜] M) (hA : Function.Injective A) (hB : Function.Surjective B) :
    finrank 𝕜 (range (A ∘ₗ L ∘ₗ B)) = finrank 𝕜 (range L) := by
  rw [range_comp, range_comp_of_range_eq_top _ (range_eq_top.2 hB)]
  exact (Submodule.equivMapOfInjective _ hA _).finrank_eq.symm

/-- If composing a map `A` of finite rank on the left with `P` does not lower the dimension of its
range, then it does not enlarge its kernel: `ker (P ∘ A) = ker A`. Indeed `P` is then injective on
the range of `A`. -/
theorem ker_comp_eq_of_finrank_range_le {K V V₂ V₃ : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (A : V →ₗ[K] V₂) (P : V₂ →ₗ[K] V₃) [FiniteDimensional K (range A)]
    (h : finrank K (range A) ≤ finrank K (range (P ∘ₗ A))) : ker (P ∘ₗ A) = ker A := by
  refine le_antisymm (fun v hv ↦ ?_) (ker_le_ker_comp A P)
  -- The restriction of `P` to the range of `A` has the same range as `P ∘ A`, hence trivial kernel.
  set P' := P ∘ₗ (range A).subtype
  have hrange : range P' = range (P ∘ₗ A) := by
    rw [range_comp, range_comp, Submodule.range_subtype]
  have hP' := P'.finrank_range_add_finrank_ker
  rw [hrange] at hP'
  have hker : ker P' = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hAv : (⟨A v, mem_range_self A v⟩ : range A) ∈ ker P' := by
    simpa [P'] using mem_ker.1 hv
  rw [hker, Submodule.mem_bot] at hAv
  exact congrArg Subtype.val hAv

end LinearMap

namespace LinearMap

/-- **Rank–nullity for a surjection**: the kernel of a surjective linear map from a
finite module has dimension the difference of the dimensions. -/
theorem finrank_ker_eq_sub_of_surjective {K : Type*} {M : Type v} {N : Type*} [Ring K]
    [HasRankNullity.{v} K] [StrongRankCondition K] [AddCommGroup M] [Module K M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (hf : Function.Surjective f) :
    Module.finrank K (ker f) = Module.finrank K M - Module.finrank K N := by
  have h := (ker f).finrank_quotient_add_finrank
  rw [(f.quotKerEquivOfSurjective hf).finrank_eq] at h
  omega

end LinearMap

namespace LinearEquiv

/-- Conjugate endomorphisms have kernels of the same dimension. -/
@[simp]
theorem finrank_ker_conj {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) :
    finrank R (LinearMap.ker (e.conj f)) = finrank R (LinearMap.ker f) := by
  rw [ker_conj, finrank_map_eq]

end LinearEquiv

end
