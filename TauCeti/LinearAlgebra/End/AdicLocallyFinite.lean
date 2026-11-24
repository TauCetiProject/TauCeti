/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Module.Submodule.Finite
public import TauCeti.LinearAlgebra.End.Basic

/-!
# Adically locally finite endomorphisms

Let `I` be an ideal of a commutative semiring `R` and `T` an endomorphism of an `R`-module `M`.
Following Pilloni, `T` is *locally finite* for `I` (`Module.End.IsLocallyFinite T I`) if for every
`n` and every `v : M` the orbit `v, T v, T² v, …` lies, modulo `I ^ n • ⊤`, in a finitely generated
submodule. No finiteness of `M` itself is required: the notion is designed for modules such as
completed direct sums of copies of `R` or completed cohomology, on which Hida's ordinary projector
is built as a limit of projectors on finite `T`-stable pieces of the quotients `M ⧸ I ^ n • ⊤`.

Over a noetherian ring the orbit condition is equivalent to asking that each finitely generated
submodule lies in a finitely generated submodule `P` with `T P ≤ P ⊔ I ^ n • ⊤`; those `P` are the
finite `T`-stable pieces just mentioned. Local finiteness passes to quotients and to products of
commuting endomorphisms. Over a noetherian ring it is also stable under extensions and passes to
submodules of a module killed by a power of `I`, and it is detected modulo `I`.

## Main definitions

* `Module.End.IsLocallyFinite T I`: modulo each `I ^ n • ⊤`, every `T`-orbit lies in a finitely
  generated submodule.

## Main results

* `Module.End.exists_fg_le_comap_of_forall_pow_apply_mem_sup`: over a noetherian ring, if every
  orbit lies in a finitely generated submodule modulo a `T`-stable `K`, every finitely generated
  submodule lies in a finitely generated submodule which is `T`-stable modulo `K`.
* `Module.End.isLocallyFinite_iff_exists_fg_le_comap`: over a noetherian ring, local finiteness
  says that every vector lies in a finitely generated submodule which is `T`-stable modulo
  `I ^ n • ⊤`.
* `Module.End.isLocallyFinite_iff_forall_mapQ_pow`: local finiteness says that in every quotient
  `M ⧸ I ^ n • ⊤` every orbit lies in a finitely generated submodule, that is, the induced
  endomorphism is locally finite for the zero ideal (`Module.End.isLocallyFinite_mapQ_bot_iff`).
* `Module.End.isLocallyFinite_of_finite`, `Module.End.isLocallyFinite_of_range_le_smul_top`:
  every endomorphism of a finite module, and every endomorphism with range in `I • ⊤`, is locally
  finite.
* `Polynomial.not_isLocallyFinite_mulLeft_X`: multiplication by `X` on `R[X]` is not locally
  finite for the zero ideal.
* `Module.End.IsLocallyFinite.of_surjective`, `Module.End.IsLocallyFinite.of_exact`,
  `Module.End.IsLocallyFinite.of_injective`: local finiteness passes to quotients, to extensions,
  and to submodules of a module killed by a power of `I`.
* `Module.End.IsLocallyFinite.mul`: the product of commuting locally finite endomorphisms is
  locally finite.
* `Module.End.isLocallyFinite_mapQ_smul_top_iff`: over a noetherian ring, `T` is locally finite
  exactly when the induced endomorphism of `M ⧸ I • ⊤` is.

## References

* V. Pilloni, *Higher coherent cohomology and p-adic modular forms of singular weights*,
  Duke Math. J. 169 (2020), §2.1, Definition 2.1.1 and Lemmas 2.1.1–2.1.2.
* G. Boxer, F. Calegari, T. Gee, V. Pilloni, *Abelian surfaces over totally real fields are
  potentially modular*, Publ. Math. IHÉS 134 (2021), §2.11, Definition 2.11.1 and
  Lemmas 2.11.2–2.11.3.
-/

public section

namespace Module.End

open Submodule

section CommSemiring

variable {R M M₂ M₃ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]

/-- An endomorphism `T` of `M` is *locally finite* for the ideal `I` if for every `n` and every
`v : M`, the orbit `(T ^ k) v` lies in `N ⊔ I ^ n • ⊤` for one finitely generated submodule `N`.
Equivalently, in every quotient `M ⧸ I ^ n • ⊤` every orbit lies in a finitely generated
submodule (`Module.End.isLocallyFinite_iff_forall_mapQ_pow`). -/
def IsLocallyFinite (T : Module.End R M) (I : Ideal R) : Prop :=
  ∀ (n : ℕ) (v : M), ∃ N : Submodule R M, N.FG ∧ ∀ k : ℕ, (T ^ k) v ∈ N ⊔ I ^ n • ⊤

variable {T : Module.End R M} {I : Ideal R}

/-- Unfolding lemma for `Module.End.IsLocallyFinite`. -/
theorem isLocallyFinite_iff : T.IsLocallyFinite I ↔
    ∀ (n : ℕ) (v : M), ∃ N : Submodule R M, N.FG ∧ ∀ k : ℕ, (T ^ k) v ∈ N ⊔ I ^ n • ⊤ :=
  Iff.rfl

/-- Local finiteness for an ideal `I` implies local finiteness for every larger ideal. -/
theorem IsLocallyFinite.mono {J : Ideal R} (hT : T.IsLocallyFinite I) (hIJ : I ≤ J) :
    T.IsLocallyFinite J := fun n v ↦ by
  obtain ⟨N, hN, hv⟩ := hT n v
  exact ⟨N, hN, fun k ↦ sup_le_sup_left (smul_mono_left (Ideal.pow_right_mono hIJ n)) N (hv k)⟩

/-- The orbit condition gives finitely generated submodules containing a whole finitely generated
submodule's orbit modulo `I ^ n • ⊤`. -/
theorem IsLocallyFinite.exists_fg_map_pow_le (hT : T.IsLocallyFinite I) (n : ℕ)
    {N : Submodule R M} (hN : N.FG) :
    ∃ P : Submodule R M, P.FG ∧ ∀ k : ℕ, N.map (T ^ k) ≤ P ⊔ I ^ n • ⊤ := by
  induction N, hN using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨P, hP, hx⟩ := hT n x
    exact ⟨P, hP, fun k ↦ by simpa [map_span] using hx k⟩
  | sup N₁ N₂ _ _ ih₁ ih₂ =>
    obtain ⟨P₁, hP₁, h₁⟩ := ih₁
    obtain ⟨P₂, hP₂, h₂⟩ := ih₂
    refine ⟨P₁ ⊔ P₂, hP₁.sup hP₂, fun k ↦ ?_⟩
    rw [Submodule.map_sup]
    exact sup_le ((h₁ k).trans (sup_le_sup_right le_sup_left _))
      ((h₂ k).trans (sup_le_sup_right le_sup_right _))

/-- A finitely generated submodule which is `T`-stable modulo `I ^ n • ⊤` contains the orbits of
its vectors modulo `I ^ n • ⊤`; this is the easy half of
`isLocallyFinite_iff_exists_fg_le_comap`, which needs no noetherian hypothesis. -/
theorem isLocallyFinite_of_forall_exists_fg_le_comap
    (h : ∀ (n : ℕ) (v : M), ∃ N : Submodule R M, N.FG ∧ v ∈ N ∧ N ≤ (N ⊔ I ^ n • ⊤).comap T) :
    T.IsLocallyFinite I := fun n v ↦ by
  obtain ⟨N, hN, hv, hNT⟩ := h n v
  exact ⟨N, hN, fun k ↦ N.le_comap_pow_of_le_comap_sup hNT (smul_top_le_comap_smul_top _ T) k hv⟩

/-! ### Examples -/

/-- Every endomorphism of a finitely generated module is locally finite. -/
@[simp]
theorem isLocallyFinite_of_finite [Module.Finite R M] : T.IsLocallyFinite I :=
  fun _ _ ↦ ⟨⊤, Module.Finite.fg_top, fun _ ↦ mem_sup_left mem_top⟩

/-- An endomorphism whose range lies in `I • ⊤` is locally finite: `T ^ k` maps into
`I ^ k • ⊤`, so modulo `I ^ n • ⊤` each orbit is spanned by its first `n` vectors. -/
theorem isLocallyFinite_of_range_le_smul_top (hT : LinearMap.range T ≤ I • ⊤) :
    T.IsLocallyFinite I := by
  have hpow : ∀ (k : ℕ) (v : M), (T ^ k) v ∈ I ^ k • (⊤ : Submodule R M) := by
    intro k v
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' T, mul_apply_eq_comp, pow_succ I, Submodule.mul_smul]
      have : (I ^ k • ⊤ : Submodule R M).map T ≤ I ^ k • I • ⊤ := by
        rw [map_smul'', Submodule.map_top]
        exact smul_mono_right _ hT
      exact this (mem_map_of_mem ih)
  intro n v
  refine ⟨span R (Set.range fun i : Fin n ↦ (T ^ (i : ℕ)) v), fg_span (Set.finite_range _),
    fun k ↦ ?_⟩
  rcases lt_or_ge k n with hk | hk
  · exact mem_sup_left (subset_span ⟨⟨k, hk⟩, rfl⟩)
  · exact mem_sup_right (smul_mono_left (Ideal.pow_le_pow_right hk) (hpow k v))

@[simp]
theorem isLocallyFinite_zero : (0 : Module.End R M).IsLocallyFinite I :=
  isLocallyFinite_of_range_le_smul_top (by simp)

@[simp]
theorem isLocallyFinite_one : (1 : Module.End R M).IsLocallyFinite I :=
  fun _ v ↦ ⟨R ∙ v, fg_span_singleton v, fun _ ↦ by simp [mem_sup_left]⟩

/-! ### Stability -/

/-- Local finiteness passes to quotients: if `g` is surjective and intertwines `T₂` with `T₃`,
then `T₃` is locally finite when `T₂` is. -/
theorem IsLocallyFinite.of_surjective {T₂ : Module.End R M₂} {T₃ : Module.End R M₃}
    {g : M₂ →ₗ[R] M₃} (hg : Function.Surjective g) (hgT : g ∘ₗ T₂ = T₃ ∘ₗ g)
    (hT : T₂.IsLocallyFinite I) : T₃.IsLocallyFinite I := by
  intro n w
  obtain ⟨v, rfl⟩ := hg w
  obtain ⟨N, hN, hv⟩ := hT n v
  refine ⟨N.map g, hN.map g, fun k ↦ ?_⟩
  rw [pow_apply_of_comp_eq hgT]
  refine (map_le_iff_le_comap.2 ?_) (mem_map_of_mem (hv k))
  exact sup_le ((le_comap_map g N).trans (comap_mono le_sup_left))
    ((smul_top_le_comap_smul_top _ g).trans (comap_mono le_sup_right))

/-- The product of commuting locally finite endomorphisms is locally finite. -/
theorem IsLocallyFinite.mul {T₁ T₂ : Module.End R M} (h : Commute T₁ T₂)
    (h₁ : T₁.IsLocallyFinite I) (h₂ : T₂.IsLocallyFinite I) : (T₁ * T₂).IsLocallyFinite I := by
  intro n v
  obtain ⟨N₁, hN₁, hv⟩ := h₁ n v
  obtain ⟨P, hP, hN₁P⟩ := h₂.exists_fg_map_pow_le n hN₁
  refine ⟨P, hP, fun k ↦ ?_⟩
  rw [h.mul_pow, (h.pow_pow k k).eq, mul_apply_eq_comp]
  have : (N₁ ⊔ I ^ n • ⊤).map (T₂ ^ k) ≤ P ⊔ I ^ n • ⊤ := by
    rw [Submodule.map_sup]
    exact sup_le (hN₁P k) ((map_le_iff_le_comap.2 (smul_top_le_comap_smul_top _ _)).trans
      le_sup_right)
  exact this (mem_map_of_mem (hv k))

/-- Powers of a locally finite endomorphism are locally finite. -/
theorem IsLocallyFinite.pow (hT : T.IsLocallyFinite I) (j : ℕ) : (T ^ j).IsLocallyFinite I := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; exact ih.mul (Commute.pow_self T j) hT

end CommSemiring

section CommRing

variable {R M M₁ M₂ M₃ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  {T : Module.End R M} {I : Ideal R}

/-! ### `T`-stable finitely generated submodules -/

/-- Over a noetherian ring, if every orbit lies in a finitely generated submodule modulo a
`T`-stable `K`, then every finitely generated submodule lies in a finitely generated submodule
which is `T`-stable modulo `K`. -/
theorem exists_fg_le_comap_of_forall_pow_apply_mem_sup [IsNoetherianRing R] {K : Submodule R M}
    (hK : K ≤ K.comap T) (h : ∀ v : M, ∃ N : Submodule R M, N.FG ∧ ∀ k : ℕ, (T ^ k) v ∈ N ⊔ K)
    {N : Submodule R M} (hN : N.FG) :
    ∃ P : Submodule R M, P.FG ∧ N ≤ P ∧ P ≤ (P ⊔ K).comap T := by
  induction N, hN using Submodule.fg_induction with
  | singleton v =>
    obtain ⟨N, hN, hv⟩ := h v
    -- The orbit span `O` is `T`-stable, and modulo `K` it is finitely generated because it lies
    -- in the image of `N`; lift its image to a finitely generated `O'` with `K ⊔ O' = K ⊔ O`.
    set O := span R (Set.range fun k ↦ (T ^ k) v)
    have hOT : O ≤ O.comap T := span_le.2 <| by
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨k + 1, by simp only [pow_succ', mul_apply_eq_comp]⟩
    have hOfg : (O.map K.mkQ).FG := by
      have : IsNoetherian R (N.map K.mkQ) := isNoetherian_of_fg_of_noetherian _ (hN.map _)
      refine FG.of_le_of_isNoetherian (T := N.map K.mkQ)
        ((map_mono (span_le.2 (Set.range_subset_iff.2 hv))).trans ?_)
      rw [Submodule.map_sup, mkQ_map_self, sup_bot_eq]
    obtain ⟨O', hO', hO'O⟩ := hOfg.exists_fg_map_eq_of_le_range (f := K.mkQ) (by simp [range_mkQ])
    have hsup : K ⊔ O' = K ⊔ O := by rw [← comap_map_mkQ, hO'O, comap_map_mkQ]
    have hS : K ⊔ O ≤ (K ⊔ O).comap T :=
      sup_le (hK.trans (comap_mono le_sup_left)) (hOT.trans (comap_mono le_sup_right))
    have hSP : K ⊔ O ≤ (O' ⊔ R ∙ v) ⊔ K := by
      rw [← hsup]
      exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
    refine ⟨O' ⊔ R ∙ v, hO'.sup (fg_span_singleton v), le_sup_right, sup_le ?_ ?_⟩
    · exact (le_sup_right.trans hsup.le).trans (hS.trans (comap_mono hSP))
    · rw [span_singleton_le_iff_mem, mem_comap]
      exact hSP (mem_sup_right (subset_span ⟨1, by simp⟩))
  | sup N₁ N₂ _ _ ih₁ ih₂ =>
    obtain ⟨P₁, hP₁, hN₁, hP₁T⟩ := ih₁
    obtain ⟨P₂, hP₂, hN₂, hP₂T⟩ := ih₂
    refine ⟨P₁ ⊔ P₂, hP₁.sup hP₂, sup_le_sup hN₁ hN₂, sup_le ?_ ?_⟩
    · exact hP₁T.trans (comap_mono (sup_le_sup_right le_sup_left _))
    · exact hP₂T.trans (comap_mono (sup_le_sup_right le_sup_right _))

/-- Over a noetherian ring, every finitely generated submodule lies in a finitely generated
submodule which is `T`-stable modulo `I ^ n • ⊤`, for a locally finite `T`. -/
theorem IsLocallyFinite.exists_fg_le_comap [IsNoetherianRing R] (hT : T.IsLocallyFinite I)
    (n : ℕ) {N : Submodule R M} (hN : N.FG) :
    ∃ P : Submodule R M, P.FG ∧ N ≤ P ∧ P ≤ (P ⊔ I ^ n • ⊤).comap T :=
  exists_fg_le_comap_of_forall_pow_apply_mem_sup (smul_top_le_comap_smul_top _ T) (hT n) hN

/-- Over a noetherian ring, `T` is locally finite exactly when, for every `n`, each vector lies in
a finitely generated submodule which is `T`-stable modulo `I ^ n • ⊤`. -/
theorem isLocallyFinite_iff_exists_fg_le_comap [IsNoetherianRing R] :
    T.IsLocallyFinite I ↔
      ∀ (n : ℕ) (v : M), ∃ N : Submodule R M, N.FG ∧ v ∈ N ∧ N ≤ (N ⊔ I ^ n • ⊤).comap T := by
  refine ⟨fun hT n v ↦ ?_, isLocallyFinite_of_forall_exists_fg_le_comap⟩
  obtain ⟨P, hP, hvP, hPT⟩ := hT.exists_fg_le_comap n (fg_span_singleton v)
  exact ⟨P, hP, (span_singleton_le_iff_mem _ _).1 hvP, hPT⟩

/-- Every endomorphism of a module whose quotients `M ⧸ I ^ n • ⊤` are finitely generated is
locally finite; for instance, when all these quotients are finite sets. -/
theorem isLocallyFinite_of_forall_finite_quotient
    (h : ∀ n : ℕ, Module.Finite R (M ⧸ I ^ n • (⊤ : Submodule R M))) : T.IsLocallyFinite I := by
  intro n v
  obtain ⟨N, hN, hNtop⟩ :=
    (h n).fg_top.exists_fg_map_eq_of_le_range (f := (I ^ n • ⊤ : Submodule R M).mkQ)
      (by simp [range_mkQ])
  refine ⟨N, hN, fun k ↦ ?_⟩
  rw [sup_comm, ← comap_map_mkQ, hNtop]
  exact mem_top

/-- The endomorphism induced by `T` on `M ⧸ K`, for a `T`-stable `K`, is locally finite for the
zero ideal exactly when every `T`-orbit lies in a finitely generated submodule modulo `K`. -/
theorem isLocallyFinite_mapQ_bot_iff {K : Submodule R M} (hK : K ≤ K.comap T) :
    IsLocallyFinite (K.mapQ K T hK) ⊥ ↔
      ∀ v : M, ∃ N : Submodule R M, N.FG ∧ ∀ k : ℕ, (T ^ k) v ∈ N ⊔ K := by
  have hgT : K.mkQ ∘ₗ T = K.mapQ K T hK ∘ₗ K.mkQ := (mapQ_mkQ _ _ _).symm
  refine ⟨fun h v ↦ ?_, fun h n w ↦ ?_⟩
  · obtain ⟨N, hN, hv⟩ := h 1 (K.mkQ v)
    obtain ⟨N₀, hN₀, rfl⟩ := hN.exists_fg_map_eq_of_le_range (f := K.mkQ) (by simp [range_mkQ])
    refine ⟨N₀, hN₀, fun k ↦ ?_⟩
    have hk := hv k
    rw [pow_one, bot_smul, sup_bot_eq, pow_apply_of_comp_eq hgT] at hk
    rw [sup_comm, ← comap_map_mkQ]
    exact mem_comap.2 hk
  · obtain ⟨v, rfl⟩ := K.mkQ_surjective w
    obtain ⟨N, hN, hv⟩ := h v
    refine ⟨N.map K.mkQ, hN.map _, fun k ↦ mem_sup_left ?_⟩
    have hk := mem_map_of_mem (f := K.mkQ) (hv k)
    rwa [Submodule.map_sup, mkQ_map_self, sup_bot_eq, ← pow_apply_of_comp_eq hgT] at hk

/-- `T` is locally finite for `I` exactly when, for every `n`, the endomorphism it induces on
`M ⧸ I ^ n • ⊤` is locally finite for the zero ideal: every orbit in that quotient lies in a
finitely generated submodule. -/
theorem isLocallyFinite_iff_forall_mapQ_pow : T.IsLocallyFinite I ↔ ∀ n : ℕ,
    IsLocallyFinite ((I ^ n • ⊤ : Submodule R M).mapQ (I ^ n • ⊤) T
      (smul_top_le_comap_smul_top _ T)) ⊥ :=
  forall_congr' fun _ ↦ (isLocallyFinite_mapQ_bot_iff _).symm

/-- Local finiteness passes to submodules of a module killed by a power of `I`: if `f` is
injective and intertwines `T₁` with `T₂`, `T₂` is locally finite and `I ^ m • ⊤ = ⊥` in `M₂`,
then `T₁` is locally finite. -/
theorem IsLocallyFinite.of_injective [IsNoetherianRing R] {T₁ : Module.End R M₁}
    {T₂ : Module.End R M₂} {f : M₁ →ₗ[R] M₂} (hf : Function.Injective f)
    (hfT : f ∘ₗ T₁ = T₂ ∘ₗ f) (hT : T₂.IsLocallyFinite I) {m : ℕ}
    (hm : I ^ m • (⊤ : Submodule R M₂) = ⊥) : T₁.IsLocallyFinite I := by
  intro n u
  obtain ⟨N, hN, hu⟩ := hT m (f u)
  have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian _ hN
  set O := span R (Set.range fun k ↦ (T₁ ^ k) u)
  have hO : O.map f ≤ N := by
    rw [map_span, span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    simpa [hm, ← pow_apply_of_comp_eq hfT] using hu k
  exact ⟨O, fg_of_fg_map_injective f hf (FG.of_le_of_isNoetherian hO),
    fun k ↦ mem_sup_left (subset_span ⟨k, rfl⟩)⟩

/-- Local finiteness is stable under extensions: if `M₁ → M₂ → M₃ → 0` is exact, the maps
intertwine `T₁`, `T₂`, `T₃`, and `T₁`, `T₃` are locally finite, then so is `T₂`. -/
theorem IsLocallyFinite.of_exact [IsNoetherianRing R] {T₁ : Module.End R M₁}
    {T₂ : Module.End R M₂} {T₃ : Module.End R M₃} {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (hfT : f ∘ₗ T₁ = T₂ ∘ₗ f)
    (hgT : g ∘ₗ T₂ = T₃ ∘ₗ g) (h₁ : T₁.IsLocallyFinite I) (h₃ : T₃.IsLocallyFinite I) :
    T₂.IsLocallyFinite I := by
  refine isLocallyFinite_of_forall_exists_fg_le_comap fun n v ↦ ?_
  -- A `T₃`-stable piece `P₃` around `g v`, lifted to `P₂ ∋ v` with `g P₂ = P₃`.
  obtain ⟨P₃, hP₃, hvP₃, hP₃T⟩ := h₃.exists_fg_le_comap n (fg_span_singleton (g v))
  obtain ⟨P₂, hP₂, hP₂P₃⟩ := hP₃.exists_fg_map_eq_of_le_range (f := g)
    (by simp [LinearMap.range_eq_top.2 hg])
  rw [span_singleton_le_iff_mem] at hvP₃
  have hmap : (P₂ ⊔ R ∙ v).map g = P₃ := by
    rw [Submodule.map_sup, hP₂P₃, map_span, Set.image_singleton, sup_eq_left,
      span_singleton_le_iff_mem]
    exact hvP₃
  -- `T₂ (P₂ ⊔ R ∙ v)` lies in `P₂ ⊔ R ∙ v ⊔ I ^ n • ⊤` up to a finitely generated part of
  -- `ker g = range f`, which is the image of a finitely generated `C₁ ≤ M₁`.
  have hK : (I ^ n • ⊤ : Submodule R M₂).map g = I ^ n • ⊤ := by
    rw [map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hg]
  have hT₂ : (P₂ ⊔ R ∙ v).map T₂ ≤ (P₂ ⊔ R ∙ v) ⊔ I ^ n • ⊤ ⊔ LinearMap.range f := by
    rw [← hfg.linearMap_ker_eq, ← comap_map_eq, Submodule.map_sup (P₂ ⊔ R ∙ v) _ g, hmap, hK,
      map_le_iff_le_comap]
    intro x hx
    have hgx : g x ∈ P₃ := hmap ▸ mem_map_of_mem hx
    have e : g (T₂ x) = T₃ (g x) := LinearMap.congr_fun hgT x
    exact mem_comap.2 (mem_comap.2 (e ▸ hP₃T hgx))
  obtain ⟨C, hC, hCf, hT₂C⟩ := ((hP₂.sup (fg_span_singleton v)).map T₂).exists_fg_le_sup hT₂
  obtain ⟨C₁, hC₁, rfl⟩ := hC.exists_fg_map_eq_of_le_range hCf
  -- A `T₁`-stable piece `P₁ ⊇ C₁`; then `P₂ ⊔ R ∙ v ⊔ f P₁` is `T₂`-stable.
  obtain ⟨P₁, hP₁, hC₁P₁, hP₁T⟩ := h₁.exists_fg_le_comap n hC₁
  refine ⟨(P₂ ⊔ R ∙ v) ⊔ P₁.map f, (hP₂.sup (fg_span_singleton v)).sup (hP₁.map f),
    mem_sup_left (mem_sup_right (mem_span_singleton_self v)), sup_le ?_ ?_⟩
  · rw [← map_le_iff_le_comap]
    exact hT₂C.trans (sup_le (sup_le_sup_right le_sup_left _)
      ((map_mono hC₁P₁).trans (le_sup_right.trans le_sup_left)))
  · rw [← map_le_iff_le_comap, ← map_comp, ← hfT, map_comp]
    refine (map_mono (map_le_iff_le_comap.2 hP₁T)).trans ?_
    rw [Submodule.map_sup]
    exact sup_le_sup le_sup_right (map_le_iff_le_comap.2 (smul_top_le_comap_smul_top _ f))

/-! ### Detection modulo `I` -/

/-- Over a noetherian ring, local finiteness is detected modulo `I`: it suffices that every orbit
lies in a finitely generated submodule modulo `I • ⊤`. -/
theorem isLocallyFinite_iff_forall_exists_fg_sup_smul_top [IsNoetherianRing R] :
    T.IsLocallyFinite I ↔
      ∀ v : M, ∃ N : Submodule R M, N.FG ∧ ∀ k : ℕ, (T ^ k) v ∈ N ⊔ I • ⊤ := by
  refine ⟨fun hT v ↦ by simpa using hT 1 v, fun h ↦ isLocallyFinite_of_forall_exists_fg_le_comap ?_⟩
  intro n
  induction n with
  | zero => exact fun v ↦ ⟨R ∙ v, fg_span_singleton v, mem_span_singleton_self v, by simp⟩
  | succ n ih =>
    intro v
    -- A piece `P ∋ v` stable modulo `I ^ n • ⊤`; its defect `C` lies in `I ^ n • W`, and a piece
    -- `Q ⊇ W` stable modulo `I • ⊤` makes `P ⊔ I ^ n • Q` stable modulo `I ^ (n + 1) • ⊤`.
    obtain ⟨P, hP, hvP, hPT⟩ := ih v
    obtain ⟨C, hC, hCI, hTP⟩ := (hP.map T).exists_fg_le_sup (map_le_iff_le_comap.2 hPT)
    obtain ⟨W, hW, -, hCW⟩ := hC.exists_fg_le_smul hCI
    obtain ⟨Q, hQ, hWQ, hQT⟩ :=
      exists_fg_le_comap_of_forall_pow_apply_mem_sup (smul_top_le_comap_smul_top I T) h hW
    refine ⟨P ⊔ I ^ n • Q, hP.sup (FG.smul (IsNoetherian.noetherian _) hQ), mem_sup_left hvP, ?_⟩
    rw [← map_le_iff_le_comap, Submodule.map_sup]
    refine sup_le (hTP.trans (sup_le (le_sup_left.trans le_sup_left) ?_)) ?_
    · exact hCW.trans ((smul_mono_right _ hWQ).trans (le_sup_right.trans le_sup_left))
    · rw [map_smul'']
      refine (smul_mono_right _ (map_le_iff_le_comap.2 hQT)).trans ?_
      rw [smul_sup, ← Submodule.mul_smul, ← pow_succ]
      exact sup_le_sup_right le_sup_right _

/-- Over a noetherian ring, `T` is locally finite exactly when the endomorphism it induces on
`M ⧸ I • ⊤` is. -/
theorem isLocallyFinite_mapQ_smul_top_iff [IsNoetherianRing R] :
    IsLocallyFinite ((I • ⊤ : Submodule R M).mapQ (I • ⊤) T (smul_top_le_comap_smul_top I T)) I ↔
      T.IsLocallyFinite I := by
  set K : Submodule R M := I • ⊤
  have hbot : (I • ⊤ : Submodule R (M ⧸ K)) = ⊥ := by
    rw [← K.range_mkQ, ← Submodule.map_top, ← map_smul'', mkQ_map_self]
  refine ⟨fun h ↦ isLocallyFinite_iff_forall_exists_fg_sup_smul_top.2 <|
    (isLocallyFinite_mapQ_bot_iff (smul_top_le_comap_smul_top I T)).1 fun _ w ↦ ?_,
    fun h ↦ h.of_surjective K.mkQ_surjective (mapQ_mkQ _ _ _).symm⟩
  -- The quotient is killed by `I`, so its orbits lie in finitely generated submodules.
  obtain ⟨N, hN, hw⟩ := h 1 w
  exact ⟨N, hN, fun k ↦ mem_sup_left (by simpa [hbot] using hw k)⟩

end CommRing

end Module.End

namespace Polynomial

variable {R : Type*} [CommSemiring R] [Nontrivial R]

/-- Multiplication by `X` on `R[X]` is not locally finite for the zero ideal: the orbit of `1`
consists of all the monomials `X ^ k`, which lie in no finitely generated submodule. -/
theorem not_isLocallyFinite_mulLeft_X :
    ¬ Module.End.IsLocallyFinite (LinearMap.mulLeft R (X : R[X])) ⊥ := by
  intro h
  obtain ⟨_, ⟨s, rfl⟩, hX⟩ := h 1 1
  obtain ⟨d, hd⟩ := span_le_degreeLE_of_finite s.finite_toSet
  have hmem := hd (by simpa [LinearMap.pow_mulLeft] using hX (d + 1))
  rw [mem_degreeLE, degree_X_pow] at hmem
  norm_cast at hmem
  omega

end Polynomial
