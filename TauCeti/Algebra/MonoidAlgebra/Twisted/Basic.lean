/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# The twisted monoid algebra of a factor set

A **factor set** on a monoid `G` with values in the units of a commutative semiring `k` is a
normalized multiplicative `2`-cocycle `α : G → G → kˣ`. The **twisted monoid algebra** `k_α[G]` is
the `k`-algebra with a basis `e g` indexed by `G` and multiplication
`e g * e h = α g h • e (g * h)`; for the trivial factor set it is the ordinary monoid algebra
`MonoidAlgebra k G`. When `G` is a group it is the twisted group algebra, the module-theoretic home
of projective representation theory: a projective representation of `G` with factor set `α` is
exactly a `k_α[G]`-module.

This file constructs the algebra as the image of the **twisted regular representation**. The
operator `TauCeti.twistedTranslation k α g` on `G →₀ k` sends the basis vector at `h` to `α g h`
times the basis vector at `g * h`, and the cocycle identity says exactly that
`twistedTranslation k α g * twistedTranslation k α h = α g h • twistedTranslation k α (g * h)`.
So the `k`-span of these operators is a subalgebra of `Module.End k (G →₀ k)`, and that subalgebra
is `TauCeti.twistedMonoidAlgebra k G α`. Associativity and unitality of the twisted product are
inherited from composition of linear maps rather than re-proved by hand, and the operators are
linearly independent -- each is recovered from its value at the basis vector of `1` -- so they form
a basis and the multiplication table above holds on the nose.

## Main definitions and results

* `TauCeti.IsFactorSet`: a normalized factor set, that is, a normalized multiplicative `2`-cocycle
  `α : G → G → kˣ`, with the pointwise product and inverse of factor sets again factor sets
  (`TauCeti.IsFactorSet.mul`, `TauCeti.IsFactorSet.inv`);
* `TauCeti.IsFactorSet.exists_eq_apply_mk`: a factor set on a group `G` that is trivial whenever
  one of its arguments lies in a normal subgroup `N` is pulled back from a factor set on `G ⧸ N`;
* `TauCeti.twistedMonoidAlgebra k G α`: the twisted monoid algebra `k_α[G]`;
* `TauCeti.TwistedMonoidAlgebra.of`: its basis elements, with the multiplication table
  `TauCeti.TwistedMonoidAlgebra.of_mul_of`, the basis `TauCeti.TwistedMonoidAlgebra.basis`, the
  dimension count `TauCeti.TwistedMonoidAlgebra.finrank_eq_natCard`, and the embedding of
  scalars `TauCeti.TwistedMonoidAlgebra.algebraMap_injective`;
* `TauCeti.TwistedMonoidAlgebra.lift`: the universal property. A family `u : G → A` in a
  `k`-algebra `A` with `u 1 = 1` and `u g * u h = α g h • u (g * h)` -- that is, a projective
  representation with factor set `α` -- extends uniquely to an algebra map `k_α[G] →ₐ[k] A`.
  For a group `G`, such a map is already determined on a generating set
  (`TauCeti.TwistedMonoidAlgebra.algHom_ext_of_closure_eq_top`);
* `TauCeti.TwistedMonoidAlgebra.monoidAlgebraEquiv`: for the trivial factor set, `k_α[G]` is the
  monoid algebra `MonoidAlgebra k G`;
* `TauCeti.TwistedMonoidAlgebra.equivOfCoboundary`: two factor sets related by
  `β g h * c (g * h) = α g h * (c g * c h)` for some `c : G → kˣ` have isomorphic twisted monoid
  algebras. For a group `G` that relation is exactly the statement that `α` and `β` are
  cohomologous, so there `k_α[G]` depends up to isomorphism only on the class of `α` in
  `H²(G, kˣ)`.

## Implementation notes

`IsFactorSet` is a `Prop`-valued class on the raw function `α`, spelled out as the multiplicative
`2`-cocycle identity `α (g * h) j * α g h = α h j * α g (h * j)` together with the normalization
`α 1 g = 1`, rather than as `groupCohomology.IsMulCocycle₂` for the trivial action of `G` on `kˣ`:
the twisted algebra wants `α` curried, and wants the normalization, which the cocycle identity
alone gives only up to the constant `α 1 1`. The other normalization `α g 1 = 1` follows from these
two (`TauCeti.IsFactorSet.one_right`). Carrying the hypotheses in a class keeps the type
`twistedMonoidAlgebra k G α` free of proof arguments.

`α g h` is the value of the factor set at the ordered pair `(g, h)`. The multiplication
`e g * e h = (α g h : k) • e (g * h)` follows the left-action convention used for projective
representations.

Nothing in the construction uses inverses in `G`, so `IsFactorSet`, the twisted algebra, its basis,
the universal property and the two comparison isomorphisms are all stated for a monoid `G`. A group
is assumed for descent to a quotient group and where an inverse appears, in
`TauCeti.IsFactorSet.apply_inv_eq_inv_apply`, `TauCeti.TwistedMonoidAlgebra.isUnit_of` and
`TauCeti.TwistedMonoidAlgebra.algHom_ext_of_closure_eq_top`.
The twisted translations themselves need only a multiplication on `G`; they are linearly
independent whenever `G` has a two-sided identity, without any factor-set identities on `α`.

`twistedMonoidAlgebra k G α` is a `Subalgebra k (Module.End k (G →₀ k))` rather than a fresh type
carrying a hand-built ring structure on `G →₀ k`. The two are the same algebra:
`TauCeti.TwistedMonoidAlgebra.basis` exhibits `G` as a basis and
`TauCeti.TwistedMonoidAlgebra.of_mul_of` is the intended multiplication table, while
`TauCeti.TwistedMonoidAlgebra.lift` and `TauCeti.TwistedMonoidAlgebra.algHom_ext` say it has the
expected universal property.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti

open Module

/-- A **normalized factor set** on a monoid `G` with values in the units of a commutative semiring
`k`: a function `α : G → G → kˣ` satisfying the multiplicative `2`-cocycle identity and normalized
at `1`. For a group `G` these are exactly the factor sets arising from projective representations
of `G` over `k`. -/
class IsFactorSet {k G : Type*} [CommSemiring k] [Monoid G] (α : G → G → kˣ) : Prop where
  /-- The multiplicative `2`-cocycle identity, the associativity constraint of the twisted
  product. -/
  cocycle (g h j : G) : α (g * h) j * α g h = α h j * α g (h * j)
  /-- Normalization on the left, half of the unitality of the twisted product. The other half,
  `α g 1 = 1`, follows from the cocycle identity (`TauCeti.IsFactorSet.one_right`). -/
  one_left (g : G) : α 1 g = 1

namespace IsFactorSet

section Monoid

variable {k G : Type*} [CommSemiring k] [Monoid G]

/-- Normalization on the right, the other half of the unitality of the twisted product: the
cocycle identity at `(g, 1, 1)` reads `α g 1 * α g 1 = α 1 1 * α g 1`, and `α 1 1 = 1`. -/
theorem one_right {α : G → G → kˣ} [self : IsFactorSet α] (g : G) : α g 1 = 1 := by
  have h := cocycle (α := α) g 1 1
  rwa [mul_one, mul_one, one_left (α := α), one_mul, mul_eq_right] at h

/-- The trivial factor set, whose twisted monoid algebra is the ordinary monoid algebra. -/
instance : IsFactorSet (1 : G → G → kˣ) where
  cocycle _ _ _ := by simp
  one_left _ := rfl

/-- The pointwise product of two factor sets is a factor set. It is the factor set of a tensor
product of projective representations (`TauCeti.IsProjectiveRep.tensorProduct`). -/
instance mul (α β : G → G → kˣ) [IsFactorSet α] [IsFactorSet β] : IsFactorSet (α * β) where
  cocycle g h j := by
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, cocycle (α := α), cocycle (α := β), mul_mul_mul_comm]
  one_left g := by simp [one_left (α := α), one_left (α := β)]

/-- The pointwise inverse of a factor set is a factor set. -/
instance inv (α : G → G → kˣ) [IsFactorSet α] : IsFactorSet α⁻¹ where
  cocycle g h j := by
    simp only [Pi.inv_apply]
    rw [← mul_inv, cocycle (α := α), mul_inv]
  one_left g := by simp [one_left (α := α)]

end Monoid

section Group

variable {k G : Type*} [CommSemiring k] [Group G] (α : G → G → kˣ) [IsFactorSet α]

/-- A factor set is symmetric on an inverse pair: it takes the same value at `(g, g⁻¹)` as at
`(g⁻¹, g)`. This is the cocycle identity at `(g, g⁻¹, g)`, and it is the coherence making the
twisted basis elements two-sided units. -/
theorem apply_inv_eq_inv_apply (g : G) : α g g⁻¹ = α g⁻¹ g := by
  simpa [one_left (α := α), one_right (α := α)] using cocycle (α := α) g g⁻¹ g

end Group

section Comp

variable {k G H : Type*} [CommSemiring k] [Monoid G] [Monoid H]

/-- The pullback of a normalized factor set along a homomorphism `f : G →* H` is a normalized
factor set. -/
theorem comp (f : G →* H) (β : H → H → kˣ) [IsFactorSet β] :
    IsFactorSet fun g₁ g₂ ↦ β (f g₁) (f g₂) where
  cocycle g₁ g₂ g₃ := by simpa only [map_mul] using cocycle (α := β) (f g₁) (f g₂) (f g₃)
  one_left g := by simpa only [map_one] using one_left (α := β) (f g)

/-- A function on `H` whose pullback along a surjective homomorphism `f : G →* H` is a normalized
factor set is itself a normalized factor set. -/
theorem of_comp {β : H → H → kˣ} (f : G →* H) (hf : Function.Surjective f)
    (h : IsFactorSet fun g₁ g₂ ↦ β (f g₁) (f g₂)) : IsFactorSet β where
  -- Each instance of the axioms on `H` is the image under `f` of one on `G`.
  cocycle a b c := by
    obtain ⟨g₁, rfl⟩ := hf a
    obtain ⟨g₂, rfl⟩ := hf b
    obtain ⟨g₃, rfl⟩ := hf c
    simpa only [map_mul] using h.cocycle g₁ g₂ g₃
  one_left a := by
    obtain ⟨g, rfl⟩ := hf a
    simpa only [map_one] using h.one_left g

end Comp

section Quotient

/-! ### Descent to a quotient group

A factor set that is trivial whenever one of its arguments lies in a normal subgroup `N` is
constant on the cosets of `N` in each argument, so it is pulled back from a factor set on `G ⧸ N`.
-/

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]
  {N : Subgroup G}

/-- A factor set that is trivial whenever its second argument lies in `N` does not change when its
second argument is multiplied on the right by an element of `N`. -/
theorem apply_mul_right_of_mem (hr : ∀ g, ∀ n ∈ N, α g n = 1) (g h : G) {n : G} (hn : n ∈ N) :
    α g (h * n) = α g h := by
  simpa [hr _ _ hn] using (cocycle (α := α) g h n).symm

/-- A factor set that is trivial whenever one of its arguments lies in the normal subgroup `N` does
not change when its first argument is multiplied on the right by an element of `N`. -/
theorem apply_mul_left_of_mem [N.Normal] (hr : ∀ g, ∀ n ∈ N, α g n = 1)
    (hl : ∀ g, ∀ n ∈ N, α n g = 1) (g h : G) {n : G} (hn : n ∈ N) :
    α (g * n) h = α g h := by
  have hc : α (g * n) h = α g (n * h) := by
    simpa [hr _ _ hn, hl _ _ hn] using cocycle (α := α) g n h
  have hconj : n * h = h * (h⁻¹ * n * h) := by simp [mul_assoc]
  rw [hc, hconj, apply_mul_right_of_mem hr g h (Subgroup.Normal.conj_mem' ‹_› n hn h)]

/-- **A factor set that is trivial whenever one of its arguments lies in the normal subgroup `N` is
inflated from `G ⧸ N`**: it is the pullback of a normalized factor set on the quotient. -/
theorem exists_eq_apply_mk [N.Normal] (hr : ∀ g, ∀ n ∈ N, α g n = 1)
    (hl : ∀ g, ∀ n ∈ N, α n g = 1) :
    ∃ β : G ⧸ N → G ⧸ N → kˣ, IsFactorSet β ∧ ∀ g h : G, α g h = β g h := by
  have hβ (a₁ b₁ a₂ b₂ : G) (ha : QuotientGroup.leftRel N a₁ a₂)
      (hb : QuotientGroup.leftRel N b₁ b₂) : α a₁ b₁ = α a₂ b₂ := by
    rw [QuotientGroup.leftRel_apply] at ha hb
    rw [← mul_inv_cancel_left a₁ a₂, ← mul_inv_cancel_left b₁ b₂,
      apply_mul_left_of_mem hr hl _ _ ha, apply_mul_right_of_mem hr _ _ hb]
  let β : G ⧸ N → G ⧸ N → kˣ := Quotient.lift₂ α hβ
  exact ⟨β, of_comp (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) ‹IsFactorSet α›,
    fun _ _ ↦ rfl⟩

end Quotient

end IsFactorSet

section Translation

variable (k : Type*) {G : Type*} [CommSemiring k]

section Mul

variable [Mul G] (α : G → G → kˣ)

/-- The `α`-twisted translation by `g` on `G →₀ k`: it sends the basis vector at `h` to `α g h`
times the basis vector at `g * h`. For the trivial factor set this is the regular representation
of `G` on its monoid algebra. -/
noncomputable def twistedTranslation (g : G) : (G →₀ k) →ₗ[k] (G →₀ k) :=
  Finsupp.lsum k fun h ↦ (α g h : k) • Finsupp.lsingle (g * h)

@[simp]
theorem twistedTranslation_single (g h : G) (b : k) :
    twistedTranslation k α g (Finsupp.single h b) = Finsupp.single (g * h) ((α g h : k) * b) := by
  simp [twistedTranslation, Finsupp.lsum_single, Finsupp.smul_single]

end Mul

/-- Twisted translations are linearly independent even without the factor-set identities:
evaluation at the basis vector of `1` gives the standard basis rescaled by units. -/
theorem linearIndependent_twistedTranslation [MulOneClass G] (α : G → G → kˣ) :
    LinearIndependent k (twistedTranslation k α) := by
  refine LinearIndependent.of_comp (LinearMap.applyₗ (Finsupp.single (1 : G) (1 : k))) ?_
  simpa only [Function.comp_def, LinearMap.applyₗ_apply_apply, twistedTranslation_single,
    Finsupp.coe_basisSingleOne, Pi.smul_def', Units.smul_def, Finsupp.smul_single,
    smul_eq_mul, mul_one] using
    (Finsupp.basisSingleOne (ι := G) (R := k)).linearIndependent.units_smul (fun g ↦ α g 1)

variable [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

@[simp]
theorem twistedTranslation_one : twistedTranslation k α 1 = 1 := by
  refine Finsupp.lhom_ext fun a b ↦ ?_
  simp [IsFactorSet.one_left]

/-- **The twisted composition law.** The composite of two twisted translations is the twisted
translation of the product, scaled by the factor set; this is the cocycle identity, restated. -/
theorem twistedTranslation_mul (g h : G) :
    twistedTranslation k α g * twistedTranslation k α h
      = (α g h : k) • twistedTranslation k α (g * h) := by
  refine Finsupp.lhom_ext fun a b ↦ ?_
  have hcoef : α g (h * a) * α h a = α g h * α (g * h) a := by
    rw [mul_comm (α g (h * a)), ← IsFactorSet.cocycle (α := α) g h a, mul_comm]
  simp only [mul_apply_eq_comp, twistedTranslation_single, LinearMap.smul_apply,
    Finsupp.smul_single, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, hcoef]

end Translation

section Algebra

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- **The twisted monoid algebra** `k_α[G]` of a factor set `α`, realized as the `k`-span of the
twisted translations inside `Module.End k (G →₀ k)`. It is a subalgebra because the cocycle
identity makes the span closed under composition (`TauCeti.twistedTranslation_mul`) and the
normalization puts the identity operator into it (`TauCeti.twistedTranslation_one`). -/
noncomputable def twistedMonoidAlgebra : Subalgebra k (Module.End k (G →₀ k)) :=
  Submodule.toSubalgebra (Submodule.span k (Set.range (twistedTranslation k α)))
    (by
      rw [← twistedTranslation_one k α]
      exact Submodule.subset_span ⟨1, rfl⟩)
    (by
      -- The span is closed under products since the products of its spanning operators are
      -- multiples of spanning operators (`TauCeti.twistedTranslation_mul`).
      refine fun x y hx hy ↦ Submodule.mul_le.1 ?_ x hx y hy
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, twistedTranslation_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g * h, rfl⟩))

@[simp]
theorem toSubmodule_twistedMonoidAlgebra :
    Subalgebra.toSubmodule (twistedMonoidAlgebra k G α) =
      Submodule.span k (Set.range (twistedTranslation k α)) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- The twisted translations lie in the twisted monoid algebra: they are its basis elements. -/
theorem twistedTranslation_mem_twistedMonoidAlgebra (g : G) :
    twistedTranslation k α g ∈ twistedMonoidAlgebra k G α := by
  rw [← Subalgebra.mem_toSubmodule, toSubmodule_twistedMonoidAlgebra]
  exact Submodule.subset_span ⟨g, rfl⟩

namespace TwistedMonoidAlgebra

variable {k G α}

/-- The basis element of `k_α[G]` at `g : G`, namely the `α`-twisted translation by `g`. -/
noncomputable def of (g : G) : twistedMonoidAlgebra k G α :=
  ⟨twistedTranslation k α g, twistedTranslation_mem_twistedMonoidAlgebra k G α g⟩

@[simp]
theorem coe_of (g : G) :
    ((of g : twistedMonoidAlgebra k G α) : Module.End k (G →₀ k)) = twistedTranslation k α g :=
  (rfl)

@[simp]
theorem of_one : (of 1 : twistedMonoidAlgebra k G α) = 1 :=
  Subtype.ext <| by simp

/-- **The multiplication table of the twisted monoid algebra**: `e g * e h = α g h • e (g * h)`. -/
@[simp]
theorem of_mul_of (g h : G) :
    (of g : twistedMonoidAlgebra k G α) * of h = (α g h : k) • of (g * h) :=
  Subtype.ext <| by simpa using twistedTranslation_mul k α g h

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- The basis elements are units, with `(α g g⁻¹)⁻¹ • e g⁻¹` as a two-sided inverse. -/
theorem isUnit_of (g : G) : IsUnit (of g : twistedMonoidAlgebra k G α) := by
  refine ⟨⟨of g, (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹, ?_, ?_⟩, rfl⟩
  · simp [smul_smul, ← Units.val_mul]
  · simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]

end Group

section Ring

variable {R : Type*} [CommRing R] (β : G → G → Rˣ) [IsFactorSet β]

/-- With ring coefficients, the twisted monoid algebra is a ring. -/
noncomputable instance : Ring (twistedMonoidAlgebra R G β) :=
  -- Specify the ambient type: inference cannot recover it through the ring-to-semiring map.
  Subalgebra.toRing (A := Module.End R (G →₀ R)) _

end Ring

variable (k G α)

/-- The twisted translations form a basis of `k_α[G]` indexed by `G`: the twisted monoid algebra is
free with basis the elements `TauCeti.TwistedMonoidAlgebra.of`. -/
noncomputable def basis : Basis G k (twistedMonoidAlgebra k G α) :=
  Basis.span (linearIndependent_twistedTranslation k α)

@[simp]
theorem basis_apply (g : G) : basis k G α g = of g :=
  Subtype.ext <| Basis.coe_span_apply _ _

instance : Module.Free k (twistedMonoidAlgebra k G α) :=
  Module.Free.of_basis (basis k G α)

/-- The twisted monoid algebra has dimension `#G`, as the ordinary monoid algebra does. For an
infinite `G` both sides are `0`. -/
theorem finrank_eq_natCard [StrongRankCondition k] :
    finrank k (twistedMonoidAlgebra k G α) = Nat.card G :=
  finrank_eq_nat_card_basis (basis k G α)

variable {k G α}

/-- Cancellation of addition transfers from the coefficients to a twisted monoid algebra. -/
instance [IsCancelAdd k] : IsCancelAdd (twistedMonoidAlgebra k G α) :=
  (basis k G α).repr.injective.isCancelAdd _ (map_add _)

@[simp]
theorem repr_of (g : G) : (basis k G α).repr (of g) = Finsupp.single g 1 := by
  rw [← basis_apply, Module.Basis.repr_self]

@[simp]
theorem repr_one : (basis k G α).repr 1 = Finsupp.single 1 1 := by
  rw [← of_one, repr_of]

/-- The coefficients of a product are the twisted convolution of the two coefficient families. -/
theorem repr_mul (f g : twistedMonoidAlgebra k G α) :
    (basis k G α).repr (f * g) =
      ((basis k G α).repr f).sum fun a r ↦
        ((basis k G α).repr g).sum fun b s ↦
          Finsupp.single (a * b) (r * s * (α a b : k)) := by
  classical
  conv_lhs =>
    rw [← (basis k G α).linearCombination_repr f, ← (basis k G α).linearCombination_repr g]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul_sum, smul_mul_smul_comm,
    map_sum, map_smul, basis_apply, of_mul_of, repr_of, Finsupp.smul_single, smul_eq_mul, mul_one]

open scoped Pointwise

/-- The coefficient support of a twisted product lies in the product of the two supports. -/
theorem support_repr_mul_subset [DecidableEq G] (f g : twistedMonoidAlgebra k G α) :
    ((basis k G α).repr (f * g)).support ⊆
      ((basis k G α).repr f).support * ((basis k G α).repr g).support := by
  rw [repr_mul]
  grw [Finsupp.support_sum, Finset.biUnion_subset]
  intro a ha
  grw [Finsupp.support_sum, Finset.biUnion_subset]
  exact fun b hb ↦ Finsupp.support_single_subset.trans <|
    Finset.singleton_subset_iff.mpr (Finset.mem_image₂_of_mem ha hb)

/-- If no pair in the supports of `f` and `g` other than `(a, b)` has product `a * b`, the
coefficient of `f * g` at `a * b` is
`(basis k G α).repr f a * (basis k G α).repr g b * α a b`. -/
theorem repr_mul_apply_of_uniqueMul {f g : twistedMonoidAlgebra k G α} {a b : G}
    (h : UniqueMul ((basis k G α).repr f).support ((basis k G α).repr g).support a b) :
    (basis k G α).repr (f * g) (a * b) =
      (basis k G α).repr f a * (basis k G α).repr g b * (α a b : k) := by
  classical
  rw [repr_mul]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [← Finset.sum_product']
  refine (Finset.sum_eq_single (a, b) ?_ ?_).trans (ite_eq_left rfl)
  · intro p hp hpne
    rw [Finset.mem_product] at hp
    exact ite_eq_right fun he ↦ hpne (Prod.ext (h hp.1 hp.2 he).1 (h hp.1 hp.2 he).2)
  · intro hab
    simp only [Finset.mem_product, not_and_or] at hab
    rcases hab with ha | hb
    · simp [Finsupp.notMem_support_iff.mp ha]
    · simp [Finsupp.notMem_support_iff.mp hb]

section MonoidCoefficients

variable {R H : Type*} [CommSemiring R] [Monoid H]
  {β : H → H → Rˣ} [IsFactorSet β]

/-- Right multiplication by a normalized basis element expands as a single weighted sum. -/
theorem repr_mul_of (f : twistedMonoidAlgebra R H β) (b : H) :
    (basis R H β).repr (f * of b) =
      ((basis R H β).repr f).sum fun a r ↦ Finsupp.single (a * b) (r * (β a b : R)) := by
  rw [repr_mul, repr_of]
  simp only [Finsupp.sum_single_index, zero_mul, mul_zero, Finsupp.single_zero, mul_one]

/-- Left multiplication by a normalized basis element expands as a single weighted sum. -/
theorem repr_of_mul (f : twistedMonoidAlgebra R H β) (b : H) :
    (basis R H β).repr (of b * f) =
      ((basis R H β).repr f).sum fun a r ↦ Finsupp.single (b * a) (r * (β b a : R)) := by
  rw [repr_mul, repr_of]
  simp only [Finsupp.sum_single_index, zero_mul, Finsupp.single_zero,
    Finsupp.sum_fun_zero, one_mul]

/-- The coefficient at `a * b` when no support index other than `a` maps there under right
multiplication by `b`; the coefficient at `a` is allowed to be zero. -/
theorem repr_mul_of_apply_of_unique (f : twistedMonoidAlgebra R H β) (a b : H)
    (h : ∀ x ∈ ((basis R H β).repr f).support, x * b = a * b → x = a) :
    (basis R H β).repr (f * of b) (a * b) =
      (basis R H β).repr f a * (β a b : R) := by
  classical
  have h' : UniqueMul ((basis R H β).repr f).support
      ((basis R H β).repr (of b)).support a b := by
    intro x y hx hy hxy
    have hyb : y = b := Finset.mem_singleton.mp (Finsupp.support_single_subset
      (by simpa only [repr_of] using hy))
    subst y
    exact ⟨h x hx hxy, rfl⟩
  simpa only [repr_of, Finsupp.single_eq_same, mul_one] using repr_mul_apply_of_uniqueMul h'

/-- The coefficient at `b * a` when no support index other than `a` maps there under left
multiplication by `b`; the coefficient at `a` is allowed to be zero. -/
theorem repr_of_mul_apply_of_unique (f : twistedMonoidAlgebra R H β) (a b : H)
    (h : ∀ x ∈ ((basis R H β).repr f).support, b * x = b * a → x = a) :
    (basis R H β).repr (of b * f) (b * a) =
      (basis R H β).repr f a * (β b a : R) := by
  classical
  have h' : UniqueMul ((basis R H β).repr (of b)).support
      ((basis R H β).repr f).support b a := by
    intro x y hx hy hxy
    have hxb : x = b := Finset.mem_singleton.mp (Finsupp.support_single_subset
      (by simpa only [repr_of] using hx))
    subst x
    exact ⟨rfl, h y hy hxy⟩
  simpa only [repr_of, Finsupp.single_eq_same, one_mul] using repr_mul_apply_of_uniqueMul h'

/-- The shifted coefficient formula when the right multiplying index is right regular. -/
theorem repr_mul_of_apply_of_isRightRegular (f : twistedMonoidAlgebra R H β) (a b : H)
    (hb : IsRightRegular b) :
    (basis R H β).repr (f * of b) (a * b) =
      (basis R H β).repr f a * (β a b : R) :=
  repr_mul_of_apply_of_unique f a b fun _ _ h ↦ hb h

/-- The shifted coefficient formula when the left multiplying index is left regular. -/
theorem repr_of_mul_apply_of_isLeftRegular (f : twistedMonoidAlgebra R H β) (a b : H)
    (hb : IsLeftRegular b) :
    (basis R H β).repr (of b * f) (b * a) =
      (basis R H β).repr f a * (β b a : R) :=
  repr_of_mul_apply_of_unique f a b fun _ _ h ↦ hb h

/-- The coefficient of right multiplication by a basis element, with its shifted index. -/
@[simp]
theorem repr_mul_of_apply [IsRightCancelMul H] (f : twistedMonoidAlgebra R H β) (a b : H) :
    (basis R H β).repr (f * of b) (a * b) =
      (basis R H β).repr f a * (β a b : R) :=
  repr_mul_of_apply_of_isRightRegular f a b fun _ _ h ↦ mul_right_cancel h

/-- The coefficient of left multiplication by a basis element, with its shifted index. -/
@[simp]
theorem repr_of_mul_apply [IsLeftCancelMul H] (f : twistedMonoidAlgebra R H β) (a b : H) :
    (basis R H β).repr (of b * f) (b * a) =
      (basis R H β).repr f a * (β b a : R) :=
  repr_of_mul_apply_of_isLeftRegular f a b fun _ _ h ↦ mul_left_cancel h

/-- A coefficient outside the right translate of the actual coefficient support vanishes. -/
theorem repr_mul_of_apply_eq_zero (f : twistedMonoidAlgebra R H β) (b c : H)
    (hc : c ∉ (fun a : H ↦ a * b) '' ↑((basis R H β).repr f).support) :
    (basis R H β).repr (f * of b) c = 0 := by
  classical
  apply Finsupp.notMem_support_iff.mp
  intro hn
  have hs := (support_repr_mul_subset f (of b)).trans
    (Finset.mul_subset_mul_left (s := ((basis R H β).repr f).support)
      (by simpa only [repr_of] using
        (Finsupp.support_single_subset : (Finsupp.single b (1 : R)).support ⊆ {b})))
  apply hc
  simpa only [Finset.coe_mul, Finset.coe_singleton, Set.mul_singleton] using
    (Finset.mem_coe.mpr (hs hn))

/-- A coefficient outside the left translate of the actual coefficient support vanishes. -/
theorem repr_of_mul_apply_eq_zero (f : twistedMonoidAlgebra R H β) (b c : H)
    (hc : c ∉ (fun a : H ↦ b * a) '' ↑((basis R H β).repr f).support) :
    (basis R H β).repr (of b * f) c = 0 := by
  classical
  apply Finsupp.notMem_support_iff.mp
  intro hn
  have hs := (support_repr_mul_subset (of b) f).trans
    (Finset.mul_subset_mul_right (t := ((basis R H β).repr f).support)
      (by simpa only [repr_of] using
        (Finsupp.support_single_subset : (Finsupp.single b (1 : R)).support ⊆ {b})))
  apply hc
  simpa only [Finset.coe_mul, Finset.coe_singleton, Set.singleton_mul] using
    (Finset.mem_coe.mpr (hs hn))

/-- The coefficient at a free index after right multiplication by a unit-index basis element. -/
@[simp]
theorem repr_mul_of_unit_apply (f : twistedMonoidAlgebra R H β) (b : Hˣ) (c : H) :
    (basis R H β).repr (f * of (b : H)) c =
      (basis R H β).repr f (c * ↑b⁻¹) * (β (c * ↑b⁻¹) b : R) := by
  simpa only [Units.inv_mul_cancel_right] using
    repr_mul_of_apply_of_isRightRegular f (c * ↑b⁻¹) (b : H)
      (fun _ _ h ↦ (Units.mul_left_inj b).mp h)

/-- The coefficient at a free index after left multiplication by a unit-index basis element. -/
@[simp]
theorem repr_of_unit_mul_apply (f : twistedMonoidAlgebra R H β) (b : Hˣ) (c : H) :
    (basis R H β).repr (of (b : H) * f) c =
      (basis R H β).repr f (↑b⁻¹ * c) * (β b (↑b⁻¹ * c) : R) := by
  simpa only [Units.mul_inv_cancel_left] using
    repr_of_mul_apply_of_isLeftRegular f (↑b⁻¹ * c) (b : H)
      (fun _ _ h ↦ (Units.mul_right_inj b).mp h)

end MonoidCoefficients

section GroupCoefficients

variable {R H : Type*} [CommSemiring R] [Group H]
  {β : H → H → Rˣ} [IsFactorSet β]

/-- The coefficient at a free index after right multiplication by a basis element. -/
@[simp]
theorem repr_mul_of_apply_mul_inv (f : twistedMonoidAlgebra R H β) (b c : H) :
    (basis R H β).repr (f * of b) c =
      (basis R H β).repr f (c * b⁻¹) * (β (c * b⁻¹) b : R) :=
  repr_mul_of_unit_apply f (toUnits b) c

/-- The coefficient at a free index after left multiplication by a basis element. -/
@[simp]
theorem repr_of_mul_apply_inv_mul (f : twistedMonoidAlgebra R H β) (b c : H) :
    (basis R H β).repr (of b * f) c =
      (basis R H β).repr f (b⁻¹ * c) * (β b (b⁻¹ * c) : R) :=
  repr_of_unit_mul_apply f (toUnits b) c

end GroupCoefficients

/-- An algebra map out of `k_α[G]` is determined by its values on the basis elements. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra k A]
    {f g : twistedMonoidAlgebra k G α →ₐ[k] A} (h : ∀ x : G, f (of x) = g (of x)) : f = g :=
  AlgHom.toLinearMap_injective <| (basis k G α).ext fun x ↦ by simpa using h x

/-- The scalar semiring embeds in `k_α[G]`, as the coefficients at the identity. -/
theorem algebraMap_injective :
    Function.Injective (algebraMap k (twistedMonoidAlgebra k G α)) := by
  have key (r : k) : (basis k G α).repr (algebraMap k _ r) 1 = r := by
    rw [Algebra.algebraMap_eq_smul_one, ← of_one, ← basis_apply, map_smul, Basis.repr_self,
      Finsupp.smul_single_one, Finsupp.single_eq_same]
  intro r s h
  rw [← key r, h, key s]

instance : FaithfulSMul k (twistedMonoidAlgebra k G α) :=
  (faithfulSMul_iff_algebraMap_injective k _).mpr algebraMap_injective

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- An algebra map out of `k_α[G]` is determined by its values on the basis elements at a
generating set of the group. -/
theorem algHom_ext_of_closure_eq_top {A : Type*} [Semiring A] [Algebra k A]
    {f g : twistedMonoidAlgebra k G α →ₐ[k] A} {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ x ∈ s, f (of x) = g (of x)) : f = g := by
  refine algHom_ext fun x ↦ ?_
  induction hs ▸ Subgroup.mem_top x using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    -- `of x * of y = α x y • of (x * y)`, so `of (x * y)` is a scalar multiple of a product.
    have key : (of (x * y) : twistedMonoidAlgebra k G α) =
        (((α x y)⁻¹ : kˣ) : k) • (of x * of y) := by
      rw [of_mul_of, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [key, map_smul, map_smul, map_mul, map_mul, hx, hy]
  | inv x _ hx =>
    -- `of x⁻¹ * of x = α x⁻¹ x • 1`, so `of x⁻¹` is a scalar multiple of the inverse of `of x`.
    obtain ⟨U, hU⟩ := isUnit_of (α := α) x
    have key : (of x⁻¹ : twistedMonoidAlgebra k G α) = (α x⁻¹ x : k) • (↑U⁻¹ : _) := by
      rw [← smul_one_mul, ← of_one, ← inv_mul_cancel x, ← of_mul_of, mul_assoc, ← hU,
        Units.mul_inv, mul_one]
    have hfg : Units.map (f : _ →* A) U = Units.map (g : _ →* A) U :=
      Units.ext <| by simpa [hU] using hx
    rw [key, map_smul, map_smul]
    congr 1
    simpa using congrArg (fun v : Aˣ ↦ ((v⁻¹ : Aˣ) : A)) hfg

end Group

section Lift

variable {A : Type*}

/-- The linear extension of a family `u : G → A` along the basis takes the value `u g` at the
basis element `TauCeti.TwistedMonoidAlgebra.of g`. -/
theorem constr_of [AddCommMonoid A] [Module k A] (u : G → A) (g : G) :
    (basis k G α).constr k u (of g) = u g := by
  rw [← basis_apply k G α g]
  exact Basis.constr_basis (b := basis k G α) (S := k) u g

variable [Semiring A] [Algebra k A]

/-- **The universal property of the twisted monoid algebra.** A projective representation of `G`
with factor set `α` in a `k`-algebra `A` -- a family `u : G → A` with `u 1 = 1` and
`u g * u h = α g h • u (g * h)` -- extends to an algebra map `k_α[G] →ₐ[k] A`. Uniqueness is
`TauCeti.TwistedMonoidAlgebra.algHom_ext`. -/
noncomputable def lift (u : G → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h : G, u g * u h = (α g h : k) • u (g * h)) :
    twistedMonoidAlgebra k G α →ₐ[k] A :=
  AlgHom.ofLinearMap ((basis k G α).constr k u)
    (by rw [← of_one (α := α), constr_of, hu₁])
    (by
      -- Multiplicativity is an equality of bilinear maps, so it suffices to check it on pairs of
      -- basis elements, where it is the hypothesis `hu`.
      have key : (LinearMap.mul k _).compr₂ ((basis k G α).constr k u) =
          (LinearMap.mul k A).compl₁₂ ((basis k G α).constr k u) ((basis k G α).constr k u) :=
        (basis k G α).ext fun g ↦ (basis k G α).ext fun h ↦ by simp [constr_of, hu]
      exact LinearMap.congr_fun₂ key)

@[simp]
theorem lift_of (u : G → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h : G, u g * u h = (α g h : k) • u (g * h)) (g : G) :
    lift u hu₁ hu (of g) = u g :=
  constr_of u g

end Lift

section DomCongr

variable {R G H : Type*} [CommSemiring R] [Monoid G] [Monoid H]
  {α : G → G → Rˣ} {β : H → H → Rˣ} [IsFactorSet α] [IsFactorSet β]

/-- A multiplicative equivalence preserving the factor set reindexes the twisted algebra. -/
noncomputable def domCongr (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b)) :
    twistedMonoidAlgebra R G α ≃ₐ[R] twistedMonoidAlgebra R H β := by
  let f : twistedMonoidAlgebra R G α →ₐ[R] twistedMonoidAlgebra R H β :=
    lift (fun a ↦ of (e a)) (by simp) (by intro a b; simp [of_mul_of, h])
  let g : twistedMonoidAlgebra R H β →ₐ[R] twistedMonoidAlgebra R G α :=
    lift (fun b ↦ of (e.symm b)) (by simp) (by
      intro a b
      have hh := h (e.symm a) (e.symm b)
      simpa only [map_mul, e.apply_symm_apply, of_mul_of] using
        congrArg (fun r : Rˣ ↦ (r : R) •
          (of (e.symm a * e.symm b) : twistedMonoidAlgebra R G α)) hh)
  exact AlgEquiv.ofAlgHom f g (by ext a; simp [f, g]) (by ext a; simp [f, g])

/-- Reindexing sends each normalized basis element to its corresponding basis element. -/
@[simp]
theorem domCongr_of (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b)) (a : G) :
    domCongr e h (of a) = of (e a) := by
  simp only [domCongr, AlgEquiv.ofAlgHom_apply, lift_of]

/-- Inverse reindexing is reindexing by the inverse monoid equivalence. -/
@[simp]
theorem domCongr_symm (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b)) :
    (domCongr e h).symm = domCongr e.symm (fun a b ↦ by
      simpa only [e.apply_symm_apply] using (h (e.symm a) (e.symm b)).symm) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro b
  apply (domCongr e h).injective
  simp only [AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply, domCongr_of,
    e.apply_symm_apply]

/-- Inverse reindexing sends each normalized basis element to its inverse-index basis element. -/
theorem domCongr_symm_of (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b)) (b : H) :
    (domCongr e h).symm (of b) = of (e.symm b) := by
  rw [domCongr_symm, domCongr_of]

/-- The underlying linear equivalence is the canonical basis transport. -/
theorem domCongr_toLinearEquiv (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b)) :
    (domCongr e h).toLinearEquiv = (basis R G α).equiv (basis R H β) e.toEquiv := by
  apply LinearEquiv.toLinearMap_injective
  apply (basis R G α).ext
  intro a
  -- The induced linear maps evaluate as their underlying equivalences.
  change (domCongr e h) ((basis R G α) a) =
    ((basis R G α).equiv (basis R H β) e.toEquiv) ((basis R G α) a)
  rw [Module.Basis.equiv_apply, basis_apply, basis_apply, domCongr_of]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]

/-- Coefficients at corresponding indices are unchanged by twist-preserving reindexing. -/
@[simp]
theorem repr_domCongr_apply (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b))
    (f : twistedMonoidAlgebra R G α) (a : G) :
    (basis R H β).repr (domCongr e h f) (e a) = (basis R G α).repr f a := by
  have hr : ((basis R H β).reindex e.toEquiv.symm).repr (domCongr e h f) =
      (basis R G α).repr f := by
    rw [← AlgEquiv.toLinearEquiv_apply, domCongr_toLinearEquiv]
    simp only [Module.Basis.equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hc := congrArg (fun v ↦ v a) hr
  simpa only [Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using hc

/-- Inverse reindexing preserves coefficients at inverse-corresponding indices. -/
theorem repr_domCongr_symm_apply (e : G ≃* H) (h : ∀ a b, α a b = β (e a) (e b))
    (f : twistedMonoidAlgebra R H β) (b : H) :
    (basis R G α).repr ((domCongr e h).symm f) (e.symm b) = (basis R H β).repr f b := by
  rw [domCongr_symm, repr_domCongr_apply]

end DomCongr

section Trivial

variable (k G)

/-- For the trivial factor set the basis elements multiply exactly as the group elements do, so
they assemble into an algebra map to the monoid algebra. -/
noncomputable def toMonoidAlgebra :
    twistedMonoidAlgebra k G (1 : G → G → kˣ) →ₐ[k] MonoidAlgebra k G :=
  lift (fun g ↦ MonoidAlgebra.single g (1 : k)) (by simp [MonoidAlgebra.one_def]) (by simp)

@[simp]
theorem toMonoidAlgebra_of (g : G) :
    toMonoidAlgebra k G (of g) = MonoidAlgebra.single g (1 : k) :=
  lift_of ..

/-- For the trivial factor set the basis elements form a copy of `G` inside `k_1[G]`, giving an
algebra map from the monoid algebra by its universal property. -/
noncomputable def fromMonoidAlgebra :
    MonoidAlgebra k G →ₐ[k] twistedMonoidAlgebra k G (1 : G → G → kˣ) :=
  MonoidAlgebra.lift k _ G ⟨⟨of, of_one⟩, fun g h ↦ by simp [of_mul_of]⟩

@[simp]
theorem fromMonoidAlgebra_single (g : G) :
    fromMonoidAlgebra k G (MonoidAlgebra.single g (1 : k)) = of g := by
  simp [fromMonoidAlgebra]

/-- **The twisted monoid algebra of the trivial factor set is the monoid algebra.** -/
noncomputable def monoidAlgebraEquiv :
    twistedMonoidAlgebra k G (1 : G → G → kˣ) ≃ₐ[k] MonoidAlgebra k G :=
  AlgEquiv.ofAlgHom (toMonoidAlgebra k G) (fromMonoidAlgebra k G) (by ext g; simp) (by ext g; simp)

@[simp]
theorem monoidAlgebraEquiv_of (g : G) :
    monoidAlgebraEquiv k G (of g) = MonoidAlgebra.single g (1 : k) :=
  toMonoidAlgebra_of k G g

end Trivial

section Coboundary

variable (α) (β : G → G → kˣ) [IsFactorSet β]

/-- A function exhibiting two factor sets as differing by a coboundary is automatically normalized
at `1`. -/
theorem eq_one_of_coboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) : c 1 = 1 := by
  simpa [IsFactorSet.one_left (α := α), IsFactorSet.one_left (α := β)] using hc 1 1

/-- Rescaling the basis elements by `c` carries the multiplication table of `β` to that of `α`,
giving an algebra map `k_β[G] →ₐ[k] k_α[G]`. -/
noncomputable def homOfCoboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) :
    twistedMonoidAlgebra k G β →ₐ[k] twistedMonoidAlgebra k G α :=
  lift (α := β) (fun g ↦ (c g : k) • (of g : twistedMonoidAlgebra k G α))
    (by simp [eq_one_of_coboundary α β c hc])
    (fun g h ↦ by simp [smul_smul, ← Units.val_mul, hc g h, mul_comm, mul_left_comm])

@[simp]
theorem homOfCoboundary_of (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) (g : G) :
    homOfCoboundary α β c hc (of g) = (c g : k) • of g :=
  lift_of ..

/-- **Factor sets differing by a coboundary have isomorphic twisted monoid algebras.** The
isomorphism rescales the basis element at `g` by `c g`. When `G` is a group, the hypothesis says
exactly that `α` and `β` are cohomologous, so there `k_α[G]` depends up to isomorphism only on the
class of `α` in `H²(G, kˣ)`. -/
noncomputable def equivOfCoboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) :
    twistedMonoidAlgebra k G β ≃ₐ[k] twistedMonoidAlgebra k G α :=
  AlgEquiv.ofAlgHom (homOfCoboundary α β c hc)
    (homOfCoboundary β α (fun g ↦ (c g)⁻¹) (fun g h ↦ by
      rw [← mul_inv, mul_inv_eq_mul_inv_iff_mul_eq_mul]
      exact (hc g h).symm))
    (by ext g; simp [smul_smul, ← Units.val_mul])
    (by ext g; simp [smul_smul, ← Units.val_mul])

@[simp]
theorem equivOfCoboundary_of (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) (g : G) :
    equivOfCoboundary α β c hc (of g) = (c g : k) • of g :=
  homOfCoboundary_of α β c hc g

end Coboundary

end TwistedMonoidAlgebra

end Algebra

end TauCeti
