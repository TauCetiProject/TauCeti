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

* **Strictness.** For a nilpotent endomorphism of a finite-dimensional vector space, each power
  `N ^ k` is strict, in the sense of `LinearMap.IsStrict`, from `F` shifted by `2 k` to `F`:
  `N ^ k (F (a + 2 k)) = range (N ^ k) ⊓ F a`. A vector of `F a` that is a value of `N ^ k` is
  already the value of a vector of `F (a + 2 k)`. The case `k = 1` holds over any ring:
  `Module.End.IsMonodromyFiltration.isStrict`.
* **Primitive parts.** In Deligne's lower convention the primitive part in degree `i` is the
  kernel of the map `gr_i → gr_{i - 2}` induced by `N`; its preimage in `F i` is
  `F i ⊓ N⁻¹ (F (i - 3))`. It is zero for `i > c`
  (`Module.End.IsMonodromyFiltration.inf_comap_of_lt`), and more generally `N ^ k` is injective
  on `gr_i` as soon as `c + k ≤ i`. If `N ^ k` is strict, every class of `gr_i` killed by
  `N ^ k` is represented by a vector of `ker N ^ k`; for `k = 1` this is
  `Module.End.IsMonodromyFiltration.ker_inf_sup`.
* **Primitive decomposition**, in recursive form. For `r ≥ 0` the graded piece `gr_{c + r}` is
  the direct sum of the kernel of `N ^ (r + 1) : gr_{c + r} → gr_{c - r - 2}`, which is the
  preimage of the primitive part in degree `c - r` under the isomorphism
  `N ^ r : gr_{c + r} ≅ gr_{c - r}`, and of `N gr_{c + r + 2}`. For `i < c`,
  `gr_i = N gr_{i + 2}`. Iterating these two statements, with the injectivity of the powers of
  `N` above the centre, expresses each graded piece as the direct sum of the images under powers
  of `N` of these preimages of primitive parts; only the recursive steps are stated here.

As in `TauCeti.LinearAlgebra.End.MonodromyFiltration.Basic`, statements about graded pieces are
expressed by equalities of submodules of `V`, without forming quotients. The injectivity above
the centre and the recursive primitive decomposition hold for every monodromy filtration over
any ring, and the identification of primitive parts with `gr (ker N)` holds whenever `N` is
strict. Strictness itself is proved, for vector spaces, with a Jordan-chain basis.

## Main results

* `Module.End.JordanChainBasis.isStrict_pow_monodromyFiltration` and
  `Module.End.isStrict_pow_monodromyFiltration`: strictness of the powers of `N` for the
  kernel-image filtration.
* `Module.End.IsMonodromyFiltration.isStrict_pow`: strictness of the powers of `N` for a
  monodromy filtration, centred anywhere, of an endomorphism of a finite-dimensional vector space,
  which is then nilpotent.
* `Module.End.IsMonodromyFiltration.inf_comap_pow_of_le`: `N ^ k` is injective on `gr_i` for
  `c + k ≤ i`.
* `Module.End.IsMonodromyFiltration.ker_pow_inf_sup`: if `N ^ k` is strict, the kernel of
  `N ^ k : gr_i → gr_{i - 2 k}` is the image of `ker N ^ k ⊓ F i`.
* `Module.End.IsMonodromyFiltration.inf_comap_pow_sup_map`,
  `Module.End.IsMonodromyFiltration.inf_comap_pow_inf_map_sup` and
  `Module.End.IsMonodromyFiltration.map_sup_of_lt`: the recursive primitive decomposition.

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

namespace IsMonodromyFiltration

section Semiring

variable [Semiring R] [AddCommMonoid V] [Module R V] {N : Module.End R V} {c : ℤ}
  {F : ℤ → Submodule R V}

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

/-- If `N ^ k` is strict from `F` shifted by `2 k` to `F`, the vectors of `F i` sent by `N ^ k`
into `F (i - 2 k - 1)` are, modulo `F (i - 1)`, the vectors of `F i` killed by `N ^ k`. So the
kernel of `N ^ k : gr_i → gr_{i - 2 k}` is the image of `gr_i (ker N ^ k)`, for the filtration
induced on `ker N ^ k`. Strictness holds for a nilpotent endomorphism of a finite-dimensional
vector space by `isStrict_pow`, and for `k = 1` over any ring by `isStrict`, which gives
`ker_inf_sup`. -/
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
