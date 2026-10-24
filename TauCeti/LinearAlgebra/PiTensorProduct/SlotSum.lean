/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.LinearAlgebra.PiTensorProduct.Map
import Mathlib.Data.ZMod.Defs

/-!
# Slot sums on tensor powers and contractions in characteristic two

Let `M` be a module over a commutative ring `R`, with an endomorphism `d`, and let `ι` be a finite
index type. The **slot sum** of `d` is the endomorphism of the indexed tensor power
`⨂[R] _ : ι, M` that applies `d` in one tensor factor at a time and adds the results:

```text
D (⨂ₜ i, m i) = ∑ i, m₁ ⊗ ⋯ ⊗ d (m i) ⊗ ⋯ ⊗ mₗ.
```

Over a general ring the differential of a tensor product of complexes carries Koszul signs, which
depend on an ordering of the factors and are permuted by reindexing. In characteristic two the
signs disappear, so `D` does not depend on any ordering of `ι`: it commutes with reindexing the
factors and with every family of factorwise maps commuting with `d`
(`TauCeti.PiTensorProduct.slotSum_comp_reindex`, `TauCeti.PiTensorProduct.slotSum_comp_map`), and
it squares to zero when `d` does (`TauCeti.PiTensorProduct.slotSum_comp_slotSum`). This is what
makes the tensor power of a complex a complex on which a symmetric group, and hence a wreath
product, acts without signs.

Characteristic two is needed only of the module, not of the scalars: the identities below assume
that every element of `M` is its own additive inverse, which holds over a ring of characteristic two
(`TauCeti.add_self_eq_zero_of_charTwo`) and also, for instance, for a module of `𝔽₂`-valued
cochains regarded over `ℤ`. A tensor power with at least one factor then inherits the property
(`TauCeti.PiTensorProduct.add_self_eq_zero`), so terms appearing twice cancel.

A contraction also passes to the tensor power. If `h` is a homotopy with `d h + h d = 1 - e`, where
`e` commutes with `d` (typically `e = ι ∘ π` for an augmentation `ι` and a retraction `π`), then for
a linear order on `ι` the **slot homotopy**

```text
H = ∑ i, e ⊗ ⋯ ⊗ e ⊗ h ⊗ 1 ⊗ ⋯ ⊗ 1        (`e` before the slot `i`, `h` at `i`, `1` after it)
```

satisfies `D H + H D = 1 - e ⊗ ⋯ ⊗ e` (`TauCeti.PiTensorProduct.slotSum_comp_slotHomotopy_add`):
cross terms appear twice and cancel, and the diagonal terms telescope. This is the sign-free,
characteristic-two form of the tensor trick, whose Koszul-signed version on words of every length
is formalized in `TauCeti/Algebra/Homology/Contraction/TensorTrick.lean`. The homotopy depends on
the ordering, but it need not be equivariant for anything.

Finally, a grading `ℳ` of `M` induces the total-degree grading of the tensor power
(`TauCeti.PiTensorProduct.totalDegreePiece`), spanned by pure tensors of homogeneous factors whose
degrees add up to the given degree. Factorwise maps of degrees `a i` shift total degree by
`∑ i, a i`, so the slot sum and the slot homotopy shift total degree by the degrees of `d` and `h`.
For a grading without negative pieces, the tensor power of a retraction vanishing in positive
degrees vanishes in positive total degree, while the slot homotopy of a homotopy vanishing in
degree zero vanishes in total degree zero.

These are the data with which a tensor power of the total coinduced resolution, with its
contraction by evaluation at `1`, is again a contracted resolution: the input of Evens'
multiplicative transfer, where the norm of a class is the class of the tensor power of a
representing cocycle in the tensor-induced resolution.

## Main definitions

* `TauCeti.PiTensorProduct.slotSum`: the sign-free extension of an endomorphism to a tensor power.
* `TauCeti.PiTensorProduct.slotHomotopy`: the ordered homotopy built from `e` and `h`.
* `TauCeti.PiTensorProduct.totalDegreePiece`: the total-degree grading of a tensor power.

## Main results

* `TauCeti.PiTensorProduct.add_self_eq_zero`: if every element of `M` is its own additive inverse,
  so is every element of a tensor power of `M` with at least one factor.
* `TauCeti.PiTensorProduct.slotSum_comp_slotSum`: if every element of `M` is its own additive
  inverse, the slot sum of a square-zero endomorphism squares to zero.
* `TauCeti.PiTensorProduct.slotSum_comp_slotHomotopy_add`: if every element of `M` is its own
  additive inverse, the slot homotopy contracts the tensor power, `D H + H D = 1 - e ⊗ ⋯ ⊗ e`.
* `TauCeti.PiTensorProduct.slotSum_comp_map` and `TauCeti.PiTensorProduct.slotSum_comp_reindex`:
  the slot sum commutes with factorwise maps and with reindexing.
* `TauCeti.PiTensorProduct.isHomogeneous_slotSum`, `TauCeti.PiTensorProduct.isHomogeneous_map`,
  `TauCeti.PiTensorProduct.isHomogeneous_map_update` and
  `TauCeti.PiTensorProduct.isHomogeneous_slotHomotopy`: the degrees of these maps for the
  total-degree grading.
* `TauCeti.PiTensorProduct.map_mem_totalDegreePiece_zero`,
  `TauCeti.PiTensorProduct.map_eq_zero_of_mem_totalDegreePiece_of_pos` and
  `TauCeti.PiTensorProduct.slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero`: the tensor powers of
  an augmentation and a retraction, and the slot homotopy, respect the extreme degrees.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5, for tensor powers of resolutions.
* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373, for the tensor
  trick.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280, for the tensor trick.
-/

public section

open Function
open scoped TensorProduct

universe uι uκ uR uA uM uN

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {κ : Type uκ} {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- If every element of `M` is its own additive inverse, then so is every element of a tensor
power of `M` with at least one factor. With no factors the tensor power is `R`, about which the
hypothesis on `M` says nothing. -/
theorem add_self_eq_zero [Nonempty ι] (hM : ∀ m : M, m + m = 0) (x : ⨂[R] _ : ι, M) :
    x + x = 0 := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h := (PiTensorProduct.tprod R).map_update_add m i (m i) (m i)
    rw [update_eq_self, hM, MultilinearMap.map_update_zero] at h
    rw [← smul_add, ← h, smul_zero]
  | add x y hx hy => rw [add_add_add_comm, hx, hy, add_zero]

section SlotSum

variable [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The **slot sum** of an endomorphism `f` of `M`: the endomorphism of the tensor power
`⨂[R] _ : ι, M` applying `f` in one tensor factor at a time, summed over the factors. In
characteristic two it is the differential of the tensor power of a complex. -/
noncomputable def slotSum (f : Module.End R M) : Module.End R (⨂[R] _ : ι, M) :=
  ∑ i, PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i f)

/-- On a pure tensor, the slot sum applies `f` to each factor in turn. -/
@[simp]
theorem slotSum_tprod (f : Module.End R M) (m : ι → M) :
    slotSum ι f (PiTensorProduct.tprod R m) =
      ∑ i, PiTensorProduct.tprod R (update m i (f (m i))) := by
  simp only [slotSum, LinearMap.sum_apply, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

/-- The slot sum of the zero endomorphism is zero. -/
@[simp]
theorem slotSum_zero : slotSum ι (0 : Module.End R M) = 0 := by
  ext m
  simp

/-- The slot sum is additive in the endomorphism. -/
theorem slotSum_add (f g : Module.End R M) : slotSum ι (f + g) = slotSum ι f + slotSum ι g := by
  simp only [slotSum, PiTensorProduct.map_update_add, Finset.sum_add_distrib]

/-- The slot sum commutes with scalar multiplication of the endomorphism. -/
theorem slotSum_smul (c : R) (f : Module.End R M) : slotSum ι (c • f) = c • slotSum ι f := by
  simp only [slotSum, PiTensorProduct.map_update_smul, Finset.smul_sum]

/-- **Naturality of the slot sum**: a family of factorwise maps intertwining `f'` with `f`
intertwines their slot sums. -/
theorem slotSum_comp_map {f : Module.End R M} {f' : Module.End R N} (g : ι → N →ₗ[R] M)
    (hg : ∀ i, f ∘ₗ g i = g i ∘ₗ f') :
    slotSum ι f ∘ₗ PiTensorProduct.map g = PiTensorProduct.map g ∘ₗ slotSum ι f' := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    slotSum_tprod, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simpa using LinearMap.congr_fun (hg j) (m j)
  · simp [hj]

/-- The slot sum does not depend on how the tensor factors are indexed: it commutes with
reindexing along an equivalence. -/
theorem slotSum_comp_reindex [Fintype κ] [DecidableEq κ] (f : Module.End R M) (σ : ι ≃ κ) :
    slotSum κ f ∘ₗ (PiTensorProduct.reindex R (fun _ ↦ M) σ).toLinearMap =
      (PiTensorProduct.reindex R (fun _ ↦ M) σ).toLinearMap ∘ₗ slotSum ι f := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod, slotSum_tprod, map_sum]
  rw [← σ.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun k ↦ ?_)
  rcases eq_or_ne k (σ i) with rfl | hk
  · rw [Equiv.symm_apply_apply]
    simp
  · have : σ.symm k ≠ i := fun h ↦ hk (by rw [← h, Equiv.apply_symm_apply])
    simp [hk, this]

/-- In characteristic two, **the slot sum of a square-zero endomorphism squares to zero**. Applying
`f` twice in one factor gives zero, and applying it in two distinct factors gives the same term in
either order, so these terms cancel in pairs. Characteristic two is asked only of `M`: every
element of `M` is its own additive inverse. -/
theorem slotSum_comp_slotSum (hM : ∀ m : M, m + m = 0) {f : Module.End R M} (hf : f ∘ₗ f = 0) :
    slotSum ι f ∘ₗ slotSum ι f = 0 := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, slotSum_tprod, map_sum,
    LinearMap.zero_apply]
  refine Finset.sum_sum_eq_zero_of_diag _ (fun i _ ↦ ?_) fun i _ j _ hij ↦ ?_
  · simp only [update_self, update_idem]
    rw [← LinearMap.comp_apply, hf, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · simp only [update_of_ne hij.symm, update_of_ne hij]
    have : Nonempty ι := ⟨i⟩
    rw [update_comm hij, add_self_eq_zero hM]

end SlotSum

section Grading

variable [AddCommMonoid A] [Fintype ι]

variable (ι) in
/-- The **total-degree grading** of a tensor power: the degree-`n` piece of `⨂[R] _ : ι, M` is
spanned by the pure tensors `⨂ₜ i, m i` with `m i` in the degree-`p i` piece of `ℳ` and
`∑ i, p i = n`. -/
def totalDegreePiece (ℳ : A → Submodule R M) (n : A) : Submodule R (⨂[R] _ : ι, M) :=
  Submodule.span R
    {t | ∃ (p : ι → A) (m : ι → M), (∀ i, m i ∈ ℳ (p i)) ∧ ∑ i, p i = n ∧
      PiTensorProduct.tprod R m = t}

variable {ℳ : A → Submodule R M}

/-- A pure tensor of homogeneous factors is homogeneous of the sum of their degrees. -/
theorem tprod_mem_totalDegreePiece {p : ι → A} {m : ι → M} (hm : ∀ i, m i ∈ ℳ (p i)) :
    PiTensorProduct.tprod R m ∈ totalDegreePiece ι ℳ (∑ i, p i) :=
  Submodule.subset_span ⟨p, m, hm, rfl, rfl⟩

/-- A submodule contains the degree-`n` piece of the total-degree grading exactly when it contains
every pure tensor of homogeneous factors of total degree `n`. -/
theorem totalDegreePiece_le_iff {n : A} {P : Submodule R (⨂[R] _ : ι, M)} :
    totalDegreePiece ι ℳ n ≤ P ↔
      ∀ (p : ι → A) (m : ι → M), (∀ i, m i ∈ ℳ (p i)) → ∑ i, p i = n →
        PiTensorProduct.tprod R m ∈ P := by
  rw [totalDegreePiece, Submodule.span_le]
  constructor
  · exact fun h p m hm hp ↦ h ⟨p, m, hm, hp, rfl⟩
  · rintro h _ ⟨p, m, hm, hp, rfl⟩
    exact h p m hm hp

/-- Factorwise maps of degrees `a i` shift the total degree by `∑ i, a i`. -/
theorem isHomogeneous_map {𝒩 : A → Submodule R N} {g : ι → N →ₗ[R] M} {a : ι → A}
    (hg : ∀ i, LinearMap.IsHomogeneous (g i) 𝒩 ℳ (a i)) :
    LinearMap.IsHomogeneous (PiTensorProduct.map g) (totalDegreePiece ι 𝒩)
      (totalDegreePiece ι ℳ) (∑ i, a i) := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  refine (totalDegreePiece_le_iff (P := (totalDegreePiece ι ℳ (n + ∑ i, a i)).comap _).2 ?_) hx
  rintro p m hm rfl
  rw [Submodule.mem_comap, PiTensorProduct.map_tprod, ← Finset.sum_add_distrib]
  exact tprod_mem_totalDegreePiece fun i ↦ (hg i).map_mem (hm i)

/-- A factorwise map of degree zero in every factor but one, where it has degree `a`, shifts the
total degree by `a`. -/
theorem isHomogeneous_map_update [DecidableEq ι] {𝒩 : A → Submodule R N} {g : ι → N →ₗ[R] M}
    {f : N →ₗ[R] M} {a : A} (i : ι) (hg : ∀ j ≠ i, LinearMap.IsHomogeneous (g j) 𝒩 ℳ 0)
    (hf : LinearMap.IsHomogeneous f 𝒩 ℳ a) :
    LinearMap.IsHomogeneous (PiTensorProduct.map (update g i f)) (totalDegreePiece ι 𝒩)
      (totalDegreePiece ι ℳ) a := by
  rw [← Fintype.sum_pi_single' i a]
  refine isHomogeneous_map fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simpa using hf
  · simpa [hj] using hg j hj

/-- Factorwise maps into degree zero land in total degree zero. -/
theorem map_mem_totalDegreePiece_zero {g : ι → N →ₗ[R] M} (hg : ∀ i x, g i x ∈ ℳ 0)
    (x : ⨂[R] _ : ι, N) : PiTensorProduct.map g x ∈ totalDegreePiece ι ℳ 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, PiTensorProduct.map_tprod]
    have := tprod_mem_totalDegreePiece (ℳ := ℳ) (p := fun _ : ι ↦ (0 : A))
      (m := fun i ↦ g i (m i)) fun i ↦ hg i (m i)
    rw [Finset.sum_const_zero] at this
    exact Submodule.smul_mem _ r this
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The slot sum of a homogeneous endomorphism of degree `a` raises the total degree by `a`. -/
theorem isHomogeneous_slotSum [DecidableEq ι] {f : Module.End R M} {a : A}
    (hf : LinearMap.IsHomogeneous f ℳ ℳ a) :
    LinearMap.IsHomogeneous (slotSum ι f) (totalDegreePiece ι ℳ) (totalDegreePiece ι ℳ) a :=
  Finset.sum_induction _ (LinearMap.IsHomogeneous · _ _ a) (fun _ _ ↦ .add)
    (LinearMap.isHomogeneous_zero _ _ _) fun i _ ↦
      isHomogeneous_map_update i (fun _ _ ↦ LinearMap.isHomogeneous_id ℳ) hf

/-- Factorwise maps vanishing in positive degrees kill the positive total degrees: a pure tensor
of homogeneous factors of positive total degree has a factor of positive degree. -/
theorem map_eq_zero_of_mem_totalDegreePiece_of_pos [LinearOrder A] [IsOrderedAddMonoid A]
    {π : ι → M →ₗ[R] N} (hπ : ∀ i p, 0 < p → ∀ v ∈ ℳ p, π i v = 0) {n : A} (hn : 0 < n)
    {v : ⨂[R] _ : ι, M} (hv : v ∈ totalDegreePiece ι ℳ n) : PiTensorProduct.map π v = 0 := by
  refine (totalDegreePiece_le_iff (P := LinearMap.ker (PiTensorProduct.map π)).2 ?_) hv
  rintro p m hm rfl
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
    by_contra! h
    exact hn.not_ge (Finset.sum_nonpos fun i _ ↦ h i)
  rw [LinearMap.mem_ker, PiTensorProduct.map_tprod]
  exact (PiTensorProduct.tprod R).map_coord_zero i (hπ i _ hi _ (hm i))

end Grading

section SlotHomotopy

variable [Fintype ι] [LinearOrder ι]

variable (ι) in
/-- The **slot homotopy** of a homotopy `h` relative to an endomorphism `e`, for a linear order on
the index type: the sum over the slots `i` of the tensor map applying `e` in the factors before
`i`, `h` in the factor `i` and the identity after it. When `d h + h d = 1 - e` and `e` commutes
with `d`, it contracts the tensor power in characteristic two
(`TauCeti.PiTensorProduct.slotSum_comp_slotHomotopy_add`). -/
noncomputable def slotHomotopy (e h : Module.End R M) : Module.End R (⨂[R] _ : ι, M) :=
  ∑ i, PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i h)

/-- On a pure tensor, the slot homotopy applies `e` before the slot, `h` at it and the identity
after it. -/
@[simp]
theorem slotHomotopy_tprod (e h : Module.End R M) (m : ι → M) :
    slotHomotopy ι e h (PiTensorProduct.tprod R m) =
      ∑ i, PiTensorProduct.tprod R
        (update (fun j ↦ if j < i then e (m j) else m j) i (h (m i))) := by
  simp only [slotHomotopy, LinearMap.sum_apply, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp only [update_of_ne hj]
    split_ifs <;> rfl

variable [AddCommMonoid A] {ℳ : A → Submodule R M}

/-- The slot homotopy of a homotopy of degree `a`, relative to an endomorphism of degree zero,
shifts the total degree by `a`. -/
theorem isHomogeneous_slotHomotopy {e h : Module.End R M} {a : A}
    (he : LinearMap.IsHomogeneous e ℳ ℳ 0) (hh : LinearMap.IsHomogeneous h ℳ ℳ a) :
    LinearMap.IsHomogeneous (slotHomotopy ι e h) (totalDegreePiece ι ℳ)
      (totalDegreePiece ι ℳ) a :=
  Finset.sum_induction _ (LinearMap.IsHomogeneous · _ _ a) (fun _ _ ↦ .add)
    (LinearMap.isHomogeneous_zero _ _ _) fun i _ ↦
      isHomogeneous_map_update i (fun j _ ↦ by
        split_ifs
        exacts [he, LinearMap.isHomogeneous_id ℳ]) hh

/-- For a grading without negative pieces, the slot homotopy of a homotopy vanishing in degree
zero vanishes in total degree zero: a pure tensor of homogeneous factors of total degree zero has
all its factors in degree zero. -/
theorem slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero [LinearOrder A] [IsOrderedAddMonoid A]
    {e h : Module.End R M} (hneg : ∀ p < 0, ℳ p = ⊥) (hh : ∀ v ∈ ℳ 0, h v = 0)
    {v : ⨂[R] _ : ι, M} (hv : v ∈ totalDegreePiece ι ℳ 0) : slotHomotopy ι e h v = 0 := by
  refine (totalDegreePiece_le_iff (P := LinearMap.ker (slotHomotopy ι e h)).2 ?_) hv
  rintro p m hm hp
  rw [LinearMap.mem_ker]
  by_cases hpos : ∀ j, 0 ≤ p j
  · have hp0 : ∀ j, p j = 0 := fun j ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hpos j).1 hp j (Finset.mem_univ j)
    rw [slotHomotopy_tprod]
    refine Finset.sum_eq_zero fun i _ ↦ (PiTensorProduct.tprod R).map_coord_zero i ?_
    rw [update_self]
    exact hh _ (hp0 i ▸ hm i)
  · obtain ⟨j, hj⟩ := not_forall.1 hpos
    rw [not_le] at hj
    have hmj : m j = 0 := by simpa [hneg _ hj] using hm j
    rw [(PiTensorProduct.tprod R).map_coord_zero j hmj, map_zero]

end SlotHomotopy

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- Off the diagonal, applying `d` in the slot `k` commutes with the summand of the slot homotopy
at another slot `i`, since `d` commutes with `e`; so when every element of `M` is its own additive
inverse the two composites cancel. -/
private theorem slotSum_slotHomotopy_cross (hM : ∀ m : M, m + m = 0) {d e h : Module.End R M}
    (hde : d ∘ₗ e = e ∘ₗ d) {i k : ι} (hki : k ≠ i) :
    PiTensorProduct.map (update (fun _ ↦ LinearMap.id) k d) *
        PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i h) +
      PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i h) *
        PiTensorProduct.map (update (fun _ ↦ LinearMap.id) k d) = 0 := by
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  refine (congrArg (· + _) (congrArg PiTensorProduct.map (funext fun j ↦ ?_))).trans
    (LinearMap.ext fun x ↦ have : Nonempty ι := ⟨i⟩; add_self_eq_zero hM _)
  rcases eq_or_ne j k with rfl | hjk
  · simp only [update_self, update_of_ne hki]
    split_ifs
    · exact hde
    · simp [Module.End.mul_eq_comp]
  · rcases eq_or_ne j i with rfl | hji <;> simp [*, Module.End.mul_eq_comp]

omit [Fintype ι] in
/-- On the diagonal, applying `d` and the summand of the slot homotopy at the same slot `i` in
both orders replaces `h` in the slot `i` by `d h + h d = 1 - e`: one step of the telescope. -/
private theorem slotSum_slotHomotopy_diag {d e h : Module.End R M}
    (hdh : d ∘ₗ h + h ∘ₗ d = LinearMap.id - e) (i : ι) :
    PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i d) *
        PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i h) +
      PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i h) *
        PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i d) =
      PiTensorProduct.map (update (fun j ↦ if j < i then e else LinearMap.id) i
        (LinearMap.id - e)) := by
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul,
    map_add_map_eq_map_update _ _ i fun j hj ↦ by simp [hj, Module.End.mul_eq_comp]]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simpa [Module.End.mul_eq_comp] using hdh
  · simp [hj, Module.End.mul_eq_comp]

/-- In characteristic two, **the slot homotopy contracts the tensor power**: if `h` is a homotopy
from the identity to an endomorphism `e` commuting with `d`, in the sense `d h + h d = 1 - e`,
then `D H + H D = 1 - e ⊗ ⋯ ⊗ e` for the slot sum `D` of `d` and the slot homotopy `H`.
Characteristic two is asked only of `M`: every element of `M` is its own additive inverse. -/
theorem slotSum_comp_slotHomotopy_add (hM : ∀ m : M, m + m = 0) {d e h : Module.End R M}
    (hde : d ∘ₗ e = e ∘ₗ d) (hdh : d ∘ₗ h + h ∘ₗ d = LinearMap.id - e) :
    slotSum ι d ∘ₗ slotHomotopy ι e h + slotHomotopy ι e h ∘ₗ slotSum ι d =
      LinearMap.id - PiTensorProduct.map fun _ ↦ e := by
  -- Expanding both products, the cross terms cancel and the diagonal terms telescope.
  rw [slotSum, slotHomotopy, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
    ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i _ ↦ (Finset.sum_add_distrib.symm.trans
    (Finset.sum_eq_single i (fun k _ hki ↦ slotSum_slotHomotopy_cross hM hde hki) (by simp))).trans
      (slotSum_slotHomotopy_diag hdh i)]
  -- The telescope of the diagonal terms, with `e` before the slot and the identity after it.
  have htel := (PiTensorProduct.mapMultilinear R (fun _ : ι ↦ M) (fun _ ↦ M)).map_sub_map_piecewise
    (fun _ ↦ e) (fun _ ↦ LinearMap.id) Finset.univ
  simp only [Finset.piecewise_univ, PiTensorProduct.mapMultilinear_apply, PiTensorProduct.map_id,
    Finset.mem_univ, forall_const] at htel
  rw [← neg_sub (PiTensorProduct.map fun _ ↦ e), htel, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← neg_sub e, ← PiTensorProduct.mapMultilinear_apply, MultilinearMap.map_update_neg,
    PiTensorProduct.mapMultilinear_apply]
  congr 2
  funext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.ne]
  · simp
  · simp [hj.ne, hj.ne', hj.not_gt]

end Ring

/-! The scalars need not have characteristic two. Over `ℤ`, the slot sum of a square-zero
endomorphism of a module of `𝔽₂`-vectors squares to zero, since the vectors are their own
additive inverses. -/
example (f : Module.End ℤ (ZMod 2 × ZMod 2)) (hf : f ∘ₗ f = 0) :
    slotSum (Fin 3) f ∘ₗ slotSum (Fin 3) f = 0 :=
  slotSum_comp_slotSum (by decide) hf

end TauCeti.PiTensorProduct
