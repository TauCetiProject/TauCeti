/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Filtration.Basic
public import TauCeti.LinearAlgebra.End.MonodromyFiltration.Basic

/-!
# Strictness and primitive decomposition of the monodromy filtration

Let `F` be a monodromy filtration of a nilpotent endomorphism `N`, centred at `c`. This file
proves the structure results that follow the existence and uniqueness of `F`
(Deligne, *Weil II*, 1.6.3–1.6.8). In characteristic zero they are the input for the
`𝔰𝔩₂`-action on the graded pieces of `F`, whose lowering operator is induced by `N`.

* **Strictness.** Over any ring, `N` is strict, in the sense of `LinearMap.IsStrict`, from `F`
  shifted by `2` to `F`: `N (F (a + 2)) = range N ⊓ F a`. For a nilpotent endomorphism of a
  finite-dimensional vector space, each power `N ^ k` is strict from `F` shifted by `2 k` to `F`:
  `N ^ k (F (a + 2 k)) = range (N ^ k) ⊓ F a`. A vector of `F a` that is a value of `N ^ k` is
  already the value of a vector of `F (a + 2 k)`.
* **Primitive parts.** In Deligne's lower convention the primitive part in degree `i` is the
  kernel `Module.End.primitivePart` of the map `Module.End.gradedPieceMap : gr_i → gr_{i - 2}`
  induced by `N`; its preimage in `F i` is
  `F i ⊓ N⁻¹ (F (i - 3))`. It is zero for `i > c`, since `N ^ k` is injective on `gr_i` as soon
  as `c + k ≤ i`. By strictness, every primitive class is represented by a vector of `ker N`,
  so that `gr_i (ker N)` is identified with the primitive part in degree `i`.
* **Primitive decomposition**, in recursive form. For `r ≥ 0` the graded piece `gr_{c + r}` is
  the direct sum of the kernel of `N ^ (r + 1) : gr_{c + r} → gr_{c - r - 2}`, which is the
  preimage of the primitive part in degree `c - r` under the isomorphism
  `N ^ r : gr_{c + r} ≅ gr_{c - r}`, and of `N gr_{c + r + 2}`. For `i < c`,
  `gr_i = N gr_{i + 2}`. Iterating these two statements, with the injectivity of the powers of
  `N` above the centre, expresses each graded piece as the direct sum of the images under powers
  of `N` of these preimages of primitive parts; only the recursive steps are stated here.

As in `TauCeti.LinearAlgebra.End.MonodromyFiltration.Basic`, statements about graded pieces are
mostly expressed by equalities of submodules of `V`, without forming quotients; the graded
pieces themselves, `TauCeti.GradedPiece F a`, appear for the induced maps and primitive parts.
The injectivity above the centre, the strictness of `N`, the identification of primitive parts
with `gr (ker N)` and the recursive primitive decomposition hold for every monodromy filtration
over any ring. Strictness of the higher powers of `N` is proved, for vector spaces, with a
Jordan-chain basis.

## Main results

* `Module.End.JordanChainBasis.isStrict_pow_monodromyFiltration` and
  `Module.End.isStrict_pow_monodromyFiltration`: strictness of the powers of `N` for the
  kernel-image filtration.
* `Module.End.IsMonodromyFiltration.isStrict`: over any ring, `N` is strict for a monodromy
  filtration, `N (F (a + 2)) = range N ⊓ F a`.
* `Module.End.IsMonodromyFiltration.isStrict_pow`: strictness of the powers of `N` for a
  monodromy filtration, centred anywhere, of an endomorphism of a finite-dimensional vector space,
  which is then nilpotent.
* `Module.End.gradedPieceMap` and `Module.End.primitivePart`: the map `gr_a → gr_{a - 2}` induced
  by `N` and its kernel `P_a`, the primitive part in the lower convention.
* `Module.End.IsMonodromyFiltration.gradedPiece_mapOfLE_pow_bijective`: `N ^ r` induces a
  bijection `gr_{c + r} → gr_{c - r}`.
* `Module.End.IsMonodromyFiltration.inf_comap_pow_of_le` and
  `Module.End.IsMonodromyFiltration.inf_comap_of_lt`: `N ^ k` is injective on `gr_i` for
  `c + k ≤ i`, so the primitive parts vanish above the centre.
* `Module.End.IsMonodromyFiltration.ker_pow_inf_sup` and
  `Module.End.IsMonodromyFiltration.ker_inf_sup`: the primitive part in degree `i` is the image
  of `ker N ⊓ F i`.
* `Module.End.IsMonodromyFiltration.primitivePart_eq_bot_of_lt` and
  `Module.End.IsMonodromyFiltration.gradedPieceKerEquiv`: `P_a = 0` for `a > c`, and
  `gr_a (ker N) ≅ P_a` for the filtration induced on `ker N`, a consequence of strictness.
* `Module.End.IsMonodromyFiltration.inf_comap_pow_sup_map`,
  `Module.End.IsMonodromyFiltration.inf_comap_pow_inf_map_sup` and
  `Module.End.IsMonodromyFiltration.map_sup_of_lt`: the recursive primitive decomposition.

## Implementation notes

Strictness of `N` is proved from the defining conditions alone, so it holds for modules over any
ring, without a Jordan decomposition. By `LinearMap.isStrict_iff_forall_map_add_one_inf_le` it
suffices to move `y ∈ F (a + 3)` with `N y ∈ F a` down to `F (a + 2)` without changing `N y`.
Above the centre, injectivity of `N` on graded pieces does this directly. At or below the centre,
`y` is congruent to `N ^ k z` with `z` in the opposite step, and graded surjectivity in ever
lower steps corrects `z` until `N ^ (k + 1)` kills it.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS **52** (1980), §1.6, 1.6.3–1.6.8.
-/

public section

open Submodule

namespace Module.End

variable {R K V : Type*}

namespace JordanChainBasis

variable [Semiring K] [AddCommMonoid V] [Module K V] {N : Module.End K V} {ι : Type*}

/-- In the presence of a Jordan-chain basis, the power `N ^ k` is strict for the monodromy
filtration and its shift by `2 k`: it maps the step `a + 2 k` onto the vectors of the step `a` in
its range. -/
theorem isStrict_pow_monodromyFiltration (c : N.JordanChainBasis ι) (k : ℕ) :
    LinearMap.IsStrict (N ^ k) (fun a => N.monodromyFiltration (a + 2 * k))
      N.monodromyFiltration := by
  refine (LinearMap.isStrict_iff_range_inf_le fun a => map_le_iff_le_comap.1
    ((N.map_pow_monodromyFiltration_le k _).trans_eq (by congr 1; ring))).2 fun a => ?_
  rintro _ ⟨⟨y, rfl⟩, hx⟩
  rw [SetLike.mem_coe, c.monodromyFiltration_eq_span, Basis.mem_span_image] at hx
  rw [← c.basis.linearCombination_repr ((N ^ k) y), Finsupp.linearCombination_apply]
  refine sum_mem fun ⟨i, l⟩ hp => smul_mem _ _ ?_
  have hw := hx hp
  simp only [Set.mem_ofPred_eq] at hw
  -- The coordinates of a vector of `range N ^ k` sit at depth at least `k`.
  have hl : k ≤ (l : ℕ) := by
    by_contra! hl
    have := LinearMap.congr_fun (c.basis_coord_comp_pow_eq_zero (p := ⟨i, l⟩) hl) y
    rw [LinearMap.comp_apply, Basis.coord_apply] at this
    exact (Finsupp.mem_support_iff.1 hp) this
  -- The chain vector at depth `l` is `N ^ k` of the vector at depth `l - k`, of weight
  -- larger by `2 k`.
  refine ⟨c.basis ⟨i, ⟨l - k, by omega⟩⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, c.monodromyFiltration_eq_span]
    refine subset_span ⟨⟨i, ⟨l - k, by omega⟩⟩, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    omega
  · rw [c.pow_apply_basis]
    split_ifs with h
    · exact congrArg c.basis (Sigma.ext rfl (heq_of_eq (Fin.ext (by simp only; omega))))
    · simp only at h
      omega

end JordanChainBasis

section FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {N : Module.End K V}

/-- For a nilpotent endomorphism of a finite-dimensional vector space, the power `N ^ k` is
strict for the monodromy filtration and its shift by `2 k`: it maps the step `a + 2 k` onto the
vectors of the step `a` in its range. -/
theorem isStrict_pow_monodromyFiltration (hN : IsNilpotent N) (k : ℕ) :
    LinearMap.IsStrict (N ^ k) (fun a => N.monodromyFiltration (a + 2 * k))
      N.monodromyFiltration := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hN
  exact c.isStrict_pow_monodromyFiltration k

end FiniteDimensional

section GradedPiece

open TauCeti

variable [Ring R] [AddCommGroup V] [Module R V] (N : Module.End R V) {F : ℤ → Submodule R V}

/-- The map `gr_a → gr_{a - 2}` induced on the graded pieces of a filtration `F` by an
endomorphism `N` lowering `F` by two steps. -/
noncomputable def gradedPieceMap (hF : ∀ a, (F a).map N ≤ F (a - 2)) (a : ℤ) :
    GradedPiece F a →ₗ[R] GradedPiece F (a - 2) :=
  GradedPiece.mapOfLE N (map_le_iff_le_comap.1 (hF a))
    (map_le_iff_le_comap.1 ((hF (a - 1)).trans_eq (by rw [sub_right_comm])))

variable {N} (hF : ∀ a, (F a).map N ≤ F (a - 2))

/-- The induced map on graded pieces sends the class of `x` to the class of `N x`. -/
@[simp]
theorem gradedPieceMap_mk {a : ℤ} (x : F a) :
    N.gradedPieceMap hF a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨N x, map_le_iff_le_comap.1 (hF a) x.property⟩ := by
  unfold gradedPieceMap
  exact GradedPiece.mapOfLE_mk _ _ _ x

variable (N) in
/-- The primitive part `P_a = ker (N : gr_a → gr_{a - 2})` of the graded piece `gr_a`, in the lower
convention; Deligne's `P_i = ker (N ^ (i + 1) : gr_i → gr_{-i-2})` is the upper one. For a
monodromy filtration these are the classes at the bottom of the `N`-strings. -/
noncomputable def primitivePart (a : ℤ) : Submodule R (GradedPiece F a) :=
  LinearMap.ker (N.gradedPieceMap hF a)

/-- An element of `gr_a` is primitive exactly when `N` sends it to zero in `gr_{a - 2}`. -/
theorem mem_primitivePart_iff {a : ℤ} {z : GradedPiece F a} :
    z ∈ N.primitivePart hF a ↔ N.gradedPieceMap hF a z = 0 :=
  LinearMap.mem_ker

/-- The class of `x ∈ F a` is primitive exactly when `N x ∈ F (a - 3)`. -/
@[simp]
theorem mk_mem_primitivePart_iff {a : ℤ} (x : F a) :
    Submodule.Quotient.mk x ∈ N.primitivePart hF a ↔ N x ∈ F (a - 3) := by
  rw [mem_primitivePart_iff, gradedPieceMap_mk, GradedPiece.mk_eq_zero_iff,
    show a - 2 - 1 = a - 3 by ring]

end GradedPiece

namespace IsMonodromyFiltration

section Semiring

variable [Semiring R] [AddCommMonoid V] [Module R V] {N : Module.End R V} {c : ℤ}
  {F : ℤ → Submodule R V}

/-- `N` sends `F a` into `F b` whenever `a - 2 ≤ b`. -/
private theorem apply_mem (hF : N.IsMonodromyFiltration c F) {a b : ℤ} (hb : a - 2 ≤ b) {x : V}
    (hx : x ∈ F a) : N x ∈ F b :=
  hF.monotone hb (hF.map_le a (mem_map_of_mem hx))

/-- The power `N ^ k` induces an injective map `gr_i → gr_{i - 2 k}` on the graded pieces of a
monodromy filtration centred at `c` as soon as `c + k ≤ i`. -/
theorem inf_comap_pow_of_le (hF : N.IsMonodromyFiltration c F) {k : ℕ} {i : ℤ}
    (h : c + k ≤ i) : F i ⊓ (F (i - 2 * k - 1)).comap (N ^ k) = F (i - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = c + r := ⟨(i - c).toNat, by omega⟩
  refine le_antisymm ?_ (le_inf (hF.monotone (by omega)) (hF.le_comap_pow (by omega)))
  -- `N ^ r x = N ^ (r - k) (N ^ k x)` lies in `F (c - r - 1)`, so `x ∈ F (c + r - 1)` by the
  -- injectivity of `N ^ r : gr_{c + r} → gr_{c - r}`.
  rintro x ⟨hx, hNx⟩
  rw [← hF.inf_comap_pow r]
  refine ⟨hx, ?_⟩
  rw [SetLike.mem_coe, mem_comap] at hNx ⊢
  rw [show r = (r - k) + k by omega, pow_add, _root_.mul_apply_eq_comp]
  exact hF.le_comap_pow (k := r - k) (by omega) hNx

/-- Above the centre `c`, the endomorphism `N` induces an injective map `gr_i → gr_{i - 2}`: the
primitive part `ker (N : gr_i → gr_{i - 2})` vanishes for `i > c`. -/
theorem inf_comap_of_lt (hF : N.IsMonodromyFiltration c F) {i : ℤ} (h : c < i) :
    F i ⊓ (F (i - 3)).comap N = F (i - 1) := by
  simpa [show i - 2 - 1 = i - 3 by ring] using
    hF.inf_comap_pow_of_le (k := 1) (i := i) (by omega)

/-- Below the centre `c`, the graded piece `gr_i` is the image of `gr_{i + 2}` under `N`. -/
theorem map_sup_of_lt (hF : N.IsMonodromyFiltration c F) {i : ℤ} (h : i < c) :
    (F (i + 2)).map N ⊔ F (i - 1) = F i := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = c - (r + 1 : ℕ) := ⟨(c - i - 1).toNat, by omega⟩
  refine le_antisymm (sup_le ((hF.map_le _).trans_eq (by congr 1; ring))
    (hF.monotone (by omega))) ?_
  -- `gr_{c - r - 1}` is the image of `gr_{c + r + 1}` under `N ^ (r + 1) = N ∘ N ^ r`, and
  -- `N ^ r` maps `F (c + r + 1)` into `F (c - r + 1)`.
  rw [← hF.map_pow_sup (r + 1)]
  refine sup_le_sup ?_ le_rfl
  rw [pow_succ', Module.End.mul_eq_comp, map_comp]
  exact map_mono (map_le_iff_le_comap.2 (hF.le_comap_pow (by push_cast; omega)))

end Semiring

section Ring

variable [Ring R] [AddCommGroup V] [Module R V] {N : Module.End R V} {c : ℤ}
  {F : ℤ → Submodule R V}

/-- The graded piece `gr_{c + r}` above the centre is spanned by the kernel of the map
`N ^ (r + 1) : gr_{c + r} → gr_{c - r - 2}` and the image of `gr_{c + r + 2}` under `N`. This
kernel is the preimage of the primitive part in degree `c - r` under the isomorphism
`N ^ r : gr_{c + r} ≅ gr_{c - r}`. -/
theorem inf_comap_pow_sup_map (hF : N.IsMonodromyFiltration c F) (r : ℕ) :
    F (c + r) ⊓ (F (c - r - 3)).comap (N ^ (r + 1)) ⊔ (F (c + r + 2)).map N = F (c + r) := by
  refine le_antisymm (sup_le inf_le_left ((hF.map_le _).trans_eq (by congr 1; ring))) ?_
  -- Write `N ^ (r + 1) x` as `N ^ (r + 2) y` modulo `F (c - r - 3)`, with `y ∈ F (c + r + 2)`;
  -- then `x = (x - N y) + N y`.
  intro x hx
  have hNx : (N ^ (r + 1)) x ∈ F (c - (r + 2 : ℕ)) := hF.le_comap_pow (by push_cast; omega) hx
  rw [← hF.map_pow_sup (r + 2), mem_sup] at hNx
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, hyz⟩ := hNx
  have hy' : y ∈ F (c + r + 2) := by simpa [add_assoc] using hy
  refine mem_sup.2 ⟨x - N y, ⟨sub_mem hx ?_, ?_⟩, N y, mem_map_of_mem hy', sub_add_cancel _ _⟩
  · exact hF.monotone (by omega) (hF.map_le _ (mem_map_of_mem hy'))
  · rw [SetLike.mem_coe, mem_comap, map_sub, ← _root_.mul_apply_eq_comp, ← pow_succ, ← hyz,
      add_sub_cancel_left]
    exact hF.monotone (by push_cast; omega) hz

/-- The sum in `inf_comap_pow_sup_map` is direct modulo `F (c + r - 1)`: the kernel of
`N ^ (r + 1) : gr_{c + r} → gr_{c - r - 2}` meets `N gr_{c + r + 2}` only in zero. -/
theorem inf_comap_pow_inf_map_sup (hF : N.IsMonodromyFiltration c F) (r : ℕ) :
    F (c + r) ⊓ (F (c - r - 3)).comap (N ^ (r + 1)) ⊓ ((F (c + r + 2)).map N ⊔ F (c + r - 1)) =
      F (c + r - 1) := by
  refine le_antisymm ?_ (le_inf (le_inf (hF.monotone (by omega))
    (hF.le_comap_pow (by push_cast; omega))) le_sup_right)
  -- If `x = N y + z` with `y ∈ F (c + r + 2)` and `z ∈ F (c + r - 1)`, then `N ^ (r + 2) y`
  -- lies in `F (c - r - 3)`, so `y ∈ F (c + r + 1)` by the injectivity of
  -- `N ^ (r + 2) : gr_{c + r + 2} → gr_{c - r - 2}`, and `N y ∈ F (c + r - 1)`.
  rintro x ⟨⟨-, hNx⟩, hx⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩ := mem_sup.1 hx
  have hNz : (N ^ (r + 1)) z ∈ F (c - r - 3) := hF.le_comap_pow (by push_cast; omega) hz
  have hy' : y ∈ F (c + (r + 2 : ℕ) - 1) := by
    rw [← hF.inf_comap_pow (r + 2)]
    refine ⟨by simpa [add_assoc] using hy, ?_⟩
    rw [SetLike.mem_coe, mem_comap, pow_succ, _root_.mul_apply_eq_comp]
    have := sub_mem hNx hNz
    rw [add_sub_cancel_right, mem_comap] at this
    exact hF.monotone (by push_cast; omega) this
  exact add_mem ((hF.map_le _) (mem_map_of_mem hy') |> hF.monotone (by push_cast; omega)) hz

/-- Pushing the image `N ^ (k + 1) z` of `z ∈ F (c + k)` down the filtration: if it lies in
`F (c - k - 3 - t)`, then `z` is congruent modulo `F (c + k - 1)` to an element killed by
`N ^ (k + 1)`. -/
private theorem exists_sub_mem_and_pow_apply_eq_zero (hF : N.IsMonodromyFiltration c F) (k : ℕ)
    {z : V} (hz : z ∈ F (c + k)) (t : ℕ) (hNz : (N ^ (k + 1)) z ∈ F (c - k - 3 - t)) :
    ∃ z', z - z' ∈ F (c + k - 1) ∧ (N ^ (k + 1)) z' = 0 := by
  obtain ⟨B, hB⟩ := hF.exists_eq_top_and_eq_bot
  suffices H : ∀ m t : ℕ, B ≤ t + m → ∀ z ∈ F (c + k), (N ^ (k + 1)) z ∈ F (c - k - 3 - t) →
      ∃ z', z - z' ∈ F (c + k - 1) ∧ (N ^ (k + 1)) z' = 0 from H B t (by omega) z hz hNz
  intro m
  induction m with
  | zero =>
    intro t ht z _ hNz
    refine ⟨z, by simp, ?_⟩
    rwa [(hB _).2 (by omega), mem_bot] at hNz
  | succ m ih =>
    intro t ht z hz hNz
    -- Lift `N ^ (k + 1) z` along the surjection `gr_{c + s} → gr_{c - s}`, `s = k + t + 3`.
    have hNz' : (N ^ (k + 1)) z ∈ F (c - (k + t + 3 : ℕ)) := by
      convert hNz using 2
      push_cast
      ring
    rw [← hF.map_pow_sup] at hNz'
    obtain ⟨_, ⟨w, hw, rfl⟩, u, hu, hwu⟩ := mem_sup.1 hNz'
    have hw' : (N ^ (t + 2)) w ∈ F (c + k - 1) := hF.le_comap_pow (k := t + 2) (by omega) hw
    obtain ⟨z', hz', hNz'⟩ := ih (t + 1) (by omega) (z - (N ^ (t + 2)) w)
      (sub_mem hz (hF.monotone (by omega) hw')) (by
        rw [map_sub, ← _root_.mul_apply_eq_comp, ← pow_add,
          show k + 1 + (t + 2) = k + t + 3 by ring, ← hwu, add_sub_cancel_left]
        exact hF.monotone (by omega) hu)
    refine ⟨z', ?_, hNz'⟩
    rw [show z - z' = (N ^ (t + 2)) w + (z - (N ^ (t + 2)) w - z') by abel]
    exact add_mem hw' hz'

/-- **Strictness of `N`** for its monodromy filtration: `N (F (a + 2)) = range N ⊓ F a` for every
`a`. This holds for every module over every ring. -/
theorem isStrict (hF : N.IsMonodromyFiltration c F) :
    LinearMap.IsStrict N (fun a => F (a + 2)) F := by
  obtain ⟨B, hB⟩ := hF.exists_eq_top_and_eq_bot
  -- By the one-step criterion, it suffices to lower `y ∈ F (a + 3)` with `N y ∈ F a` to
  -- `F (a + 2)` without changing `N y`.
  refine (LinearMap.isStrict_iff_forall_map_add_one_inf_le (fun _ _ h => hF.monotone (by omega))
    hF.monotone (fun a => map_le_iff_le_comap.1 ((hF.map_le _).trans_eq
      (by rw [add_sub_cancel_right])))
    (eq_top_iff.2 (le_iSup_of_le (c + B - 2) (by rw [sub_add_cancel, (hB _).1 le_rfl])))).2
    fun a => ?_
  rintro _ ⟨⟨y, hy, rfl⟩, hNy⟩
  rw [show a + 1 + 2 = a + 3 by ring] at hy
  rcases lt_or_ge c (a + 3) with hc | hc
  · -- Above the centre, `N` is injective on graded pieces, so `y` lies in `F (a + 2)`.
    refine mem_map_of_mem ?_
    rw [show a + 2 = a + 3 - 1 by ring, ← hF.inf_comap_of_lt hc]
    exact ⟨hy, hF.monotone (by omega) hNy⟩
  -- At or below the centre, write `y = N ^ k z + y₁` with `y₁ ∈ F (a + 2)` and replace `z` by an
  -- element `z'` killed by `N ^ (k + 1)`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + 3 = c - k := ⟨(c - a - 3).toNat, by omega⟩
  rw [hk, ← hF.map_pow_sup] at hy
  obtain ⟨_, ⟨z, hz, rfl⟩, y₁, hy₁, rfl⟩ := mem_sup.1 hy
  have hNy₁ : N y₁ ∈ F (c - k - 3) := hF.apply_mem (by omega) hy₁
  obtain ⟨z', hzz', hNz'⟩ := hF.exists_sub_mem_and_pow_apply_eq_zero k hz 0 (by
    rw [show (N ^ (k + 1)) z = N ((N ^ k) z + y₁) - N y₁ by
      rw [map_add, add_sub_cancel_right, pow_succ', _root_.mul_apply_eq_comp]]
    exact sub_mem (hF.monotone (by omega) hNy) (hF.monotone (by omega) hNy₁))
  have key : N ((N ^ k) (z - z') + y₁) = N ((N ^ k) z + y₁) := by
    rw [map_add, map_add, map_sub, map_sub, ← _root_.mul_apply_eq_comp N (N ^ k) z', ← pow_succ',
      hNz', sub_zero]
  rw [← key]
  exact mem_map_of_mem
    (add_mem (hF.le_comap_pow (k := k) (by omega) hzz') (hF.monotone (by omega) hy₁))

/-- If `N ^ k` is strict from `F` shifted by `2 k` to `F`, the vectors of `F i` sent by `N ^ k`
into `F (i - 2 k - 1)` are, modulo `F (i - 1)`, the vectors of `F i` killed by `N ^ k`. So the
kernel of `N ^ k : gr_i → gr_{i - 2 k}` is the image of `gr_i (ker N ^ k)`, for the filtration
induced on `ker N ^ k`. Strictness holds for a nilpotent endomorphism of a finite-dimensional
vector space by `isStrict_pow`. -/
theorem ker_pow_inf_sup (hF : N.IsMonodromyFiltration c F) {k : ℕ}
    (hs : LinearMap.IsStrict (N ^ k) (fun a => F (a + 2 * k)) F) (i : ℤ) :
    LinearMap.ker (N ^ k) ⊓ F i ⊔ F (i - 1) = F i ⊓ (F (i - 2 * k - 1)).comap (N ^ k) := by
  refine le_antisymm (sup_le (inf_comm (LinearMap.ker (N ^ k)) (F i) ▸ inf_le_inf_left _
    fun x hx => by simp [LinearMap.mem_ker.1 hx])
    (le_inf (hF.monotone (by omega)) (hF.le_comap_pow (by omega)))) ?_
  -- By strictness, `N ^ k x = N ^ k y` with `y ∈ F (i - 1)`; then `x = (x - y) + y`.
  rintro x ⟨hx, hNx⟩
  have : (N ^ k) x ∈ (F (i - 1)).map (N ^ k) := by
    rw [show i - 1 = i - 2 * k - 1 + 2 * k by ring, LinearMap.isStrict_iff.1 hs]
    exact ⟨LinearMap.mem_range_self _ _, hNx⟩
  obtain ⟨y, hy, hxy⟩ := this
  refine mem_sup.2 ⟨x - y, ⟨?_, sub_mem hx (hF.monotone (by omega) hy)⟩, y, hy,
    sub_add_cancel _ _⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hxy, sub_self]

/-- The primitive part `ker (N : gr_i → gr_{i - 2})` is the image of `gr_i (ker N)`: modulo
`F (i - 1)`, the vectors of `F i` sent by `N` into `F (i - 3)` are those killed by `N`. This is
the statement `gr_i (ker N) ≅ P_i` of `gradedPieceKerEquiv` without quotients, a consequence of
the strictness `isStrict` of `N`. -/
theorem ker_inf_sup (hF : N.IsMonodromyFiltration c F) (i : ℤ) :
    LinearMap.ker N ⊓ F i ⊔ F (i - 1) = F i ⊓ (F (i - 3)).comap N := by
  simpa [show i - 2 - 1 = i - 3 by ring] using
    hF.ker_pow_inf_sup (k := 1) (by simpa using hF.isStrict) i

open TauCeti in
/-- The primitive part `P_a` of a monodromy filtration vanishes above the centre `c`. -/
theorem primitivePart_eq_bot_of_lt (hF : N.IsMonodromyFiltration c F) {a : ℤ} (ha : c < a) :
    N.primitivePart hF.map_le a = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  induction z using Submodule.Quotient.induction_on with | _ x
  rw [mk_mem_primitivePart_iff] at hz
  rw [mem_bot, GradedPiece.mk_eq_zero_iff, ← hF.inf_comap_of_lt ha]
  exact ⟨x.property, hz⟩

open TauCeti in
/-- For a monodromy filtration centred at `c`, the map `gr_{c + r} → gr_{c - r}` induced by
`N ^ r` is bijective. -/
theorem gradedPiece_mapOfLE_pow_bijective (hF : N.IsMonodromyFiltration c F) (r : ℕ)
    (h : F (c + r) ≤ (F (c - r)).comap (N ^ r))
    (h' : F (c + r - 1) ≤ (F (c - r - 1)).comap (N ^ r)) :
    Function.Bijective (GradedPiece.mapOfLE (N ^ r) h h') := by
  rw [Function.Bijective, GradedPiece.mapOfLE_injective_iff, GradedPiece.mapOfLE_surjective_iff,
    hF.inf_comap_pow, hF.map_pow_sup]
  exact ⟨le_rfl, le_rfl⟩

open TauCeti in
/-- The map `gr_a (ker N) → gr_a` induced by the inclusion of the filtration `ker N ⊓ F` into
`F` has image the primitive part `P_a`. -/
private theorem range_gradedPiece_mapOfLE_id_eq_primitivePart
    (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    LinearMap.range (GradedPiece.mapOfLE (F := fun b => LinearMap.ker N ⊓ F b) LinearMap.id
      (p := a) (q := a) (inf_le_right.trans_eq (comap_id _).symm)
      (inf_le_right.trans_eq (comap_id _).symm)) = N.primitivePart hF.map_le a := by
  ext z
  induction z using Submodule.Quotient.induction_on with | _ y
  rw [mk_mem_primitivePart_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    induction w using Submodule.Quotient.induction_on with | _ x
    rw [GradedPiece.mapOfLE_mk, GradedPiece.mk_eq_mk_iff, Subtype.coe_mk, LinearMap.id_apply] at hw
    have hx := mem_comap.1 (mem_inf.1
      ((hF.ker_inf_sup a).le (mem_sup_left x.property))).2
    rw [show (y : V) = x - (x - y) by abel, map_sub]
    exact sub_mem hx (hF.apply_mem (by omega) hw)
  · intro hNy
    obtain ⟨x, hx, w, hw, hxw⟩ :=
      mem_sup.1 ((hF.ker_inf_sup a).ge ⟨y.property, hNy⟩)
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [GradedPiece.mapOfLE_mk, GradedPiece.mk_eq_mk_iff, ← hxw]
    simpa using hw

open TauCeti in
/-- For a monodromy filtration, the graded pieces of the filtration `ker N ⊓ F` induced on the
kernel of `N` are the primitive parts: `gr_a (ker N) ≅ P_a`, the class of `x ∈ ker N ⊓ F a`
going to its class in `gr_a`. -/
noncomputable def gradedPieceKerEquiv (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    GradedPiece (fun b => LinearMap.ker N ⊓ F b) a ≃ₗ[R] N.primitivePart hF.map_le a :=
  (LinearEquiv.ofInjective _ ((GradedPiece.mapOfLE_injective_iff _ _ _).2 fun _ hx => by
    rw [comap_id] at hx
    exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 hx).2⟩)).trans
    (LinearEquiv.ofEq _ _ (hF.range_gradedPiece_mapOfLE_id_eq_primitivePart a))

open TauCeti in
/-- The isomorphism `gr_a (ker N) ≅ P_a` sends the class of `x` to its class in `gr_a`. -/
@[simp]
theorem coe_gradedPieceKerEquiv_mk (hF : N.IsMonodromyFiltration c F) {a : ℤ}
    (x : ↥(LinearMap.ker N ⊓ F a)) :
    (hF.gradedPieceKerEquiv a (Submodule.Quotient.mk x) : GradedPiece F a) =
      Submodule.Quotient.mk ⟨x, x.property.2⟩ := by
  rw [gradedPieceKerEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]
  exact GradedPiece.mapOfLE_mk (F := fun b => LinearMap.ker N ⊓ F b) _ _ _ x

end Ring

section FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {N : Module.End K V}
  {c : ℤ} {F : ℤ → Submodule K V}

/-- A monodromy filtration of an endomorphism of a finite-dimensional vector space, which is
nilpotent by `isNilpotent`, is strict for the powers of `N`: `N ^ k` maps the step `a + 2 k` onto
the vectors of the step `a` in its range. -/
theorem isStrict_pow (hF : N.IsMonodromyFiltration c F) (k : ℕ) :
    LinearMap.IsStrict (N ^ k) (fun a => F (a + 2 * k)) F := by
  have hN := hF.isNilpotent
  obtain rfl := (isMonodromyFiltration_iff hN).1 hF
  refine LinearMap.isStrict_iff.2 fun a => ?_
  dsimp only
  rw [show a + 2 * k - c = a - c + 2 * k by ring]
  exact LinearMap.isStrict_iff.1 (isStrict_pow_monodromyFiltration hN k) (a - c)

end FiniteDimensional

end IsMonodromyFiltration

end Module.End
