/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Homogeneous linear maps

This file records the degree of a linear map between modules equipped with families of graded
subobjects. A linear map has degree `q` when it maps everything in the degree-`p` piece of the
source into the degree-`p + q` piece of the target. This is a containment condition, so no
direct-sum hypothesis is imposed and a map can be homogeneous of several degrees at once. The
families are indexed by an arbitrary `SetLike` type, so the homogeneity predicate and the additive
closure lemmas cover gradings by submodules, additive subgroups and additive submonoids alike.
`LinearMap.IsHomogeneous.smul` additionally needs the target pieces to be closed under a
distributive scalar action, and `LinearMap.homogeneousSubmodule` needs them to be additive
submonoids closed under a module action, i.e. a submodule-valued grading.

The degree index only needs an addition for the homogeneity predicate itself; the identity and
restriction lemmas also use a zero (`AddZeroClass`), composition uses associativity
(`AddSemigroup`), powers of endomorphisms use `AddMonoid`, and reindexing uses commutativity
(`AddCommSemigroup`).

The multilinear counterpart, and the degree calculus for substitution, are in
`TauCeti.LinearAlgebra.Graded.Multilinear`.

## Main definitions

* `LinearMap.IsHomogeneous`: a linear map shifts homogeneous degree by a fixed amount.
* `LinearMap.IsHomogeneous.restrict`: restriction of a degree-zero homogeneous map to each piece.
* `LinearMap.homogeneousSubmodule`: the submodule of linear maps of a fixed degree.

## Main results

* `LinearMap.IsHomogeneous.comp`: degrees add under composition of linear maps.
* `LinearMap.IsHomogeneous.pow`: the `k`-th power of an endomorphism of degree `q` has degree
  `k • q`.
* `LinearMap.isHomogeneous_span_iff`: a linear map out of a module whose pieces are spanned by
  given sets is homogeneous exactly when it moves the spanning vectors to the right degree.
* `LinearMap.IsHomogeneous.iSup_range_inf_eq`: the range of a homogeneous map out of a module
  spanned by its pieces is spanned by its intersections with the target pieces.
* `LinearMap.IsHomogeneous.restrict_zero`, `LinearMap.IsHomogeneous.restrict_id`, and
  `LinearMap.IsHomogeneous.restrict_comp`: functoriality of `IsHomogeneous.restrict`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

universe uR uι uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- If a linear map detects membership in each piece, a graded scalar action on the
target also respects the source pieces. -/
theorem gradedSMul_of_mem_iff {κ S : Type*} [SetLike S R] [VAdd κ ι]
    (f : M →ₗ[R] N) (𝒜 : κ → S) (G : ι → σM) (H : ι → σN) [SetLike.GradedSMul 𝒜 H]
    (hmem : ∀ {q x}, x ∈ G q ↔ f x ∈ H q) : SetLike.GradedSMul 𝒜 G where
  smul_mem {p q} {a x} ha hx := by
    rw [hmem, map_smul]
    exact SetLike.GradedSMul.smul_mem ha (hmem.mp hx)

section Add

variable [Add ι]

/-- A linear map is homogeneous of degree `q` if it maps the degree-`p` piece of `𝒜` into the
degree-`p + q` piece of `ℬ`. No direct-sum hypothesis on the families is needed. -/
def IsHomogeneous (f : M →ₗ[R] N) (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) : Prop :=
  ∀ ⦃p : ι⦄ ⦃x : M⦄, x ∈ 𝒜 p → f x ∈ ℬ (p + q)

/-- Homogeneity of degree `q` is exactly the mapping condition on homogeneous elements. This is a
convenient introduction rule, and `IsHomogeneous.map_mem` is the corresponding elimination rule. -/
theorem isHomogeneous_def {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    IsHomogeneous f 𝒜 ℬ q ↔ ∀ (p : ι) (x : M), x ∈ 𝒜 p → f x ∈ ℬ (p + q) :=
  ⟨fun hf _ _ hx ↦ hf hx, fun hf _ _ hx ↦ hf _ _ hx⟩

/-- Apply a homogeneous linear map to a homogeneous element. -/
theorem IsHomogeneous.map_mem {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q p : ι} (hf : IsHomogeneous f 𝒜 ℬ q) {x : M} (hx : x ∈ 𝒜 p) :
    f x ∈ ℬ (p + q) :=
  hf hx

/-- A homogeneous linear map kills a homogeneous element whose target piece is trivial. -/
theorem IsHomogeneous.apply_eq_zero_of_eq_bot {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → Submodule R N} {q p : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (hbot : ℬ (p + q) = ⊥)
    {x : M} (hx : x ∈ 𝒜 p) : f x = 0 :=
  (Submodule.mem_bot R).mp (hbot ▸ hf.map_mem hx)

/-- The zero linear map is homogeneous of every degree. -/
@[simp]
theorem isHomogeneous_zero [ZeroMemClass σN N] (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) :
    IsHomogeneous (0 : M →ₗ[R] N) 𝒜 ℬ q := by
  intro p x _
  simp

/-- A sum of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.add [AddMemClass σN N] {f g : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f + g) 𝒜 ℬ q := by
  intro p x hx
  simpa using add_mem (hf hx) (hg hx)

/-- The range of a homogeneous linear map out of a module spanned by its graded pieces is spanned
by its intersections with the target pieces. -/
theorem IsHomogeneous.iSup_range_inf_eq {f : M →ₗ[R] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} {q : ι} (hf : IsHomogeneous f ℳ 𝒩 q) (hℳ : ⨆ p, ℳ p = ⊤) :
    ⨆ p, range f ⊓ 𝒩 p = range f := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  calc range f = (⨆ p, ℳ p).map f := by rw [hℳ, range_eq_map]
    _ = ⨆ p, (ℳ p).map f := Submodule.map_iSup f ℳ
    _ ≤ ⨆ p, range f ⊓ 𝒩 p := iSup_le fun p ↦ le_iSup_of_le (p + q) <|
        le_inf map_le_range (Submodule.map_le_iff_le_comap.2 fun _ hx ↦ hf hx)

end Add

/-- The identity linear map is homogeneous of degree zero. -/
@[simp]
theorem isHomogeneous_id [AddZeroClass ι] (𝒜 : ι → σM) :
    IsHomogeneous (LinearMap.id : M →ₗ[R] M) 𝒜 𝒜 0 := by
  intro p x hx
  simpa using hx

/-- Degrees add under composition of linear maps. -/
@[grind →]
theorem IsHomogeneous.comp [AddSemigroup ι] {P : Type uP} {σP : Type*} [AddCommMonoid P]
    [Module R P] [SetLike σP P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} {𝒜 : ι → σM}
    {ℬ : ι → σN} {𝒞 : ι → σP} {q r : ι}
    (hg : IsHomogeneous g ℬ 𝒞 r) (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (g.comp f) 𝒜 𝒞 (q + r) := by
  intro p x hx
  simpa only [_root_.LinearMap.comp_apply, add_assoc] using hg (hf hx)

/-- The `k`-th power of an endomorphism of degree `q` has degree `k • q`. -/
theorem IsHomogeneous.pow [AddMonoid ι] {f : Module.End R M} {𝒜 : ι → σM} {q : ι}
    (hf : IsHomogeneous f 𝒜 𝒜 q) (k : ℕ) : IsHomogeneous (f ^ k) 𝒜 𝒜 (k • q) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simpa [pow_succ, Module.End.mul_eq_comp, succ_nsmul'] using ih.comp hf

section AddZeroClass

variable [AddZeroClass ι]

/-- A degree-zero homogeneous linear map restricts to a linear map on each graded piece. -/
def IsHomogeneous.restrict {g : M →ₗ[R] N} {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N}
    (hg : IsHomogeneous g ℳ 𝒩 0) (k : ι) : ℳ k →ₗ[R] 𝒩 k :=
  g.restrict fun _ hx ↦ by simpa only [add_zero] using hg.map_mem hx

/-- Coercing `IsHomogeneous.restrict` back to the ambient module applies the original map. -/
@[simp]
theorem IsHomogeneous.coe_restrict_apply {g : M →ₗ[R] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} (hg : IsHomogeneous g ℳ 𝒩 0) (k : ι) (x : ℳ k) :
    (hg.restrict k x : N) = g x :=
  _root_.LinearMap.coe_restrict_apply _ x

/-- Restricting the zero linear map to any graded piece gives zero. -/
@[simp]
theorem IsHomogeneous.restrict_zero {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N}
    (hg : IsHomogeneous (0 : M →ₗ[R] N) ℳ 𝒩 0) (k : ι) :
    hg.restrict k = 0 := by
  ext x
  simp

/-- Restricting the identity linear map to any graded piece gives the identity. -/
@[simp]
theorem IsHomogeneous.restrict_id {ℳ : ι → Submodule R M}
    (hg : IsHomogeneous (_root_.LinearMap.id : M →ₗ[R] M) ℳ ℳ 0) (k : ι) :
    hg.restrict k = _root_.LinearMap.id := by
  ext x
  simp

/-- Restricting a composite of degree-zero homogeneous linear maps to a graded piece is the
composite of their piece restrictions. -/
theorem IsHomogeneous.restrict_comp {P : Type uP} [AddCommMonoid P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N}
    {𝒞 : ι → Submodule R P} (hg : IsHomogeneous g 𝒩 𝒞 0) (hf : IsHomogeneous f ℳ 𝒩 0) (k : ι)
    (hcomp : IsHomogeneous (g.comp f) ℳ 𝒞 0 := by
      intro p x hx
      simpa only [_root_.LinearMap.comp_apply, add_zero] using hg (hf hx)) :
    hcomp.restrict k = (hg.restrict k).comp (hf.restrict k) := by
  ext x
  simp

end AddZeroClass

end Semiring

section Span

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN}
  [Semiring R] [Semiring S] [Add ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

/-- A linear map out of a module whose degree-`p` piece is spanned by a set `s p` has degree `q`
exactly when it maps each vector of each `s p` into the degree-`p + q` piece of the target. The
map may be linear over a larger semiring `S` than the semiring `R` of the pieces. -/
theorem isHomogeneous_span_iff {f : M →ₗ[S] N} {s : ι → Set M} {ℬ : ι → Submodule R N}
    {q : ι} :
    IsHomogeneous f (fun p ↦ Submodule.span R (s p)) ℬ q ↔ ∀ p, ∀ x ∈ s p, f x ∈ ℬ (p + q) :=
  ⟨fun hf _ _ hx ↦ hf (Submodule.subset_span hx), fun h p _ hx ↦
    (Submodule.span_le (p := (ℬ (p + q)).comap (f.restrictScalars R))).2 (h p) hx⟩

end Span

section Neg

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [Add ι] [AddCommMonoid M] [AddCommGroup N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- The negative of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.neg [NegMemClass σN N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (-f) 𝒜 ℬ q := by
  intro p x hx
  simpa using neg_mem (hf hx)

/-- A difference of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.sub [AddMemClass σN N] [NegMemClass σN N] {f g : M →ₗ[R] N}
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q)
    (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Neg

section Scalars

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN}
  {σM : Type*} {σN : Type*}
  [Semiring R] [Add ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- A scalar multiple of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.smul [DistribSMul S N] [SMulCommClass R S N]
    [SMulMemClass σN S N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (s : S) :
    IsHomogeneous (s • f) 𝒜 ℬ q := by
  intro p x hx
  simpa using SMulMemClass.smul_mem s (hf hx)

/-- Linear maps of a fixed degree form a submodule over any scalar ring acting on the target. -/
def homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N] (𝒜 : ι → σM)
    (ℬ : ι → σN) (q : ι) : Submodule S (M →ₗ[R] N) where
  carrier := {f | IsHomogeneous f 𝒜 ℬ q}
  zero_mem' := isHomogeneous_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' s _ hf := hf.smul s

/-- Membership in `homogeneousSubmodule` is homogeneity of the given degree. -/
@[simp, grind =]
theorem mem_homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N]
    {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    f ∈ homogeneousSubmodule (S := S) 𝒜 ℬ q ↔ IsHomogeneous f 𝒜 ℬ q :=
  Iff.rfl

/-- Restricting the scalars of a homogeneous linear map preserves its degree. -/
theorem IsHomogeneous.restrictScalars (R₀ : Type*) [Semiring R₀]
    [Module R₀ M] [Module R₀ N] [SMul R₀ R] [IsScalarTower R₀ R M] [IsScalarTower R₀ R N]
    {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (f.restrictScalars R₀) 𝒜 ℬ q :=
  hf

end Scalars

section Reindex

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddCommSemigroup ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Translating the indices of both gradings by the same amount preserves homogeneity. -/
theorem IsHomogeneous.reindex {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (p : ι) :
    IsHomogeneous f (fun n ↦ 𝒜 (n + p)) (fun n ↦ ℬ (n + p)) q := fun n _ hx ↦ by
  have h := hf.map_mem hx
  rwa [add_right_comm] at h

end Reindex

end LinearMap
