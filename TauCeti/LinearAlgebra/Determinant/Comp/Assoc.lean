/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Comp.Basic
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Fin
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Associativity of the composition law of determinant lines

Let `f : M → N`, `g : N → P` and `h : P → Q` be linear maps between vector spaces over a field,
with finite-dimensional kernels and cokernels. The composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) splits `det (h ∘ g ∘ f)` into
`det f ⊗ det g ⊗ det h` in two ways: first off `h`, through `det (g ∘ f) ⊗ det h`, or first off
`f`, through `det f ⊗ det (h ∘ g)`. This file proves that the two splittings agree up to an
explicit sign (`LinearMap.detLineCompEquiv_assoc`):

`assoc ((c(f, g) ⊗ 1) (c(g ∘ f, h) x)) = (-1) ^ (r₁ r₂ + r₃ r₄) • (1 ⊗ c(g, h)) (c(f, h ∘ g) x)`,

where `c` is the composition law, `r₁` and `r₄` are the ranks of the connecting maps
`ker g → coker f` and `ker h → coker g`, `r₂` is the rank of `ker (h ∘ g ∘ f) → ker h` and `r₃`
that of `coker f → coker (h ∘ g ∘ f)`.

The sign is genuine. Take `f : K → K²` the inclusion of the first coordinate line, `g : K² → K²`
the projection onto it and `h : K² → K` the second coordinate. Then `ker g → coker f` and
`ker (h ∘ g ∘ f) = K → ker h` are nonzero, so `r₁ = r₂ = 1`, while `h ∘ g = 0` and `ker h` is the
range of `g`, so `r₃ = r₄ = 0`: the two splittings differ by `-1`, a genuine sign unless `K` has
characteristic two.

The proof evaluates both sides with `LinearMap.detLineCompEquiv_tmul` on one exterior product
`β ⊗ φ`, where `β` spans `det (ker (h ∘ g ∘ f))`. It uses families of vectors adapted to all four
kernel–cokernel sequences at once, recorded in the private structure `AssocData`: a basis `u` of
`ker f` completed by `v` to `ker (g ∘ f)` and by `b` to `ker (h ∘ g ∘ f)`, vectors `w` of `ker g`
and `w₂` of `ker (h ∘ g)` whose classes, together with vectors `x`, form a basis of `coker f`,
vectors `c` of `ker h`, and lifts `y` and `e` completing bases of the cokernels of `g ∘ f`, `g`,
`h ∘ g` and `h`. Both sides then become the same tensor of exterior products and normalized
functionals, except that the factors are listed in different orders in two places. Splitting off
`h` first lists the cokernel of `g ∘ f` through the classes of `w₂`, `c`, `x`, `y`, while splitting
`g ∘ f` lists it through `w₂`, `x`, `c`, `y`. Splitting off `f` first lists `ker (h ∘ g)` through
`v`, `b`, `w`, `w₂`, while splitting `h ∘ g` lists it through `v`, `w`, `b`, `w₂`. Exchanging the
two middle blocks costs `(-1) ^ (r₃ r₄)` and `(-1) ^ (r₂ r₁)` respectively.

## Main results

* `LinearMap.detLineCompEquiv_assoc`: associativity of the composition law of determinant lines,
  up to the sign `(-1) ^ (r₁ r₂ + r₃ r₄)`.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (the compatibility
  of the composition isomorphisms with triple composites, and its signs).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K]

section Assoc

/-! ### Auxiliary linear algebra -/

/-- Lifts of a basis of the range of `p` have linearly independent images. -/
private theorem exists_linearIndependent_comp {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (p : V →ₗ[K] W) [FiniteDimensional K (range p)] :
    ∃ a : Fin (finrank K (range p)) → V, LinearIndependent K (p ∘ a) := by
  choose a ha using fun i ↦ p.surjective_rangeRestrict (Module.finBasis K (range p) i)
  refine ⟨a, ?_⟩
  have : ⇑p ∘ a = Subtype.val ∘ Module.finBasis K (range p) :=
    funext fun i ↦ congrArg Subtype.val (ha i)
  rw [this]
  exact (Module.finBasis K _).linearIndependent.map' _ (Submodule.ker_subtype _)

/-- Lifts along a surjection of a basis of its target have linearly independent images. -/
private theorem exists_linearIndependent_comp_of_surjective {V W : Type*} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p : V →ₗ[K] W}
    (hp : Function.Surjective p) :
    ∃ a : Fin (finrank K W) → V, LinearIndependent K (p ∘ a) := by
  choose a ha using fun i ↦ hp (Module.finBasis K W i)
  exact ⟨a, by rw [show ⇑p ∘ a = Module.finBasis K W from funext ha]; exact
    (Module.finBasis K W).linearIndependent⟩

/-- An exterior product of `dim V` vectors, counted through `n = dim V`, is an element of
`det V`. -/
private theorem exists_detLine_coe_eq_ιMulti {V : Type*} [AddCommGroup V] [Module K V] {n : ℕ}
    (hn : finrank K V = n) (a : Fin n → V) :
    ∃ γ : TauCeti.detLine K V, (γ : ExteriorAlgebra K V) = ExteriorAlgebra.ιMulti K n a :=
  ⟨exteriorPower.ιMulti K _ (a ∘ Fin.cast hn), by
    rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]⟩

/-- An exterior product of a linearly independent family of `dim V` vectors is a nonzero element
of `det V`, at which some functional takes the value `1`. -/
private theorem exists_detLine_coe_eq {V : Type*} [AddCommGroup V] [Module K V] {n : ℕ}
    (hn : finrank K V = n) {a : Fin n → V} (ha : LinearIndependent K a) :
    ∃ (γ : TauCeti.detLine K V) (ξ : Dual K (TauCeti.detLine K V)),
      (γ : ExteriorAlgebra K V) = ExteriorAlgebra.ιMulti K n a ∧ ξ γ = 1 := by
  have hγ : exteriorPower.ιMulti K _ (a ∘ Fin.cast hn) ≠ 0 :=
    (exteriorPower.ιMulti_ne_zero_iff _).2 (ha.comp _ (Fin.cast_injective hn))
  obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one K hγ
  exact ⟨_, ξ, by rw [exteriorPower.ιMulti_apply_coe,
    TauCeti.ExteriorAlgebra.ιMulti_comp_cast], hξ⟩

/-- Exchanging the middle two of four exterior products costs the sign of the exchange. -/
private theorem ιMulti_mul_ιMulti_mul_swap {V : Type*} [AddCommGroup V] [Module K V]
    {a b c d : ℕ} (A : Fin a → V) (B : Fin b → V) (C : Fin c → V) (D : Fin d → V) :
    ExteriorAlgebra.ιMulti K a A * (ExteriorAlgebra.ιMulti K b B *
        (ExteriorAlgebra.ιMulti K c C * ExteriorAlgebra.ιMulti K d D)) =
      (-1 : K) ^ (b * c) • (ExteriorAlgebra.ιMulti K a A * (ExteriorAlgebra.ιMulti K c C *
        (ExteriorAlgebra.ιMulti K b B * ExteriorAlgebra.ιMulti K d D))) := by
  rw [← mul_assoc (ExteriorAlgebra.ιMulti K b B),
    TauCeti.ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul B C, smul_mul_assoc,
    mul_smul_comm, mul_comm c b, mul_assoc]

/-! ### Dimension counts -/

variable {M N P Q : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  (f : M →ₗ[K] N) (g : N →ₗ[K] P) (h : P →ₗ[K] Q)

/-- The dimension counts along the kernel–cokernel sequence of a composition. -/
private theorem finrank_comp_sixTerm [FiniteDimensional K (ker f)]
    [FiniteDimensional K (ker g)] [FiniteDimensional K (N ⧸ range f)]
    [FiniteDimensional K (P ⧸ range g)] :
    finrank K (ker (g ∘ₗ f)) = finrank K (ker f) + finrank K (range (f.kerCompToKer g)) ∧
      finrank K (ker g) =
        finrank K (range (f.kerCompToKer g)) + finrank K (range (f.kerToCoker g)) ∧
      finrank K (N ⧸ range f) =
        finrank K (range (f.kerToCoker g)) + finrank K (range (f.cokerToCokerComp g)) ∧
      finrank K (P ⧸ range (g ∘ₗ f)) =
        finrank K (range (f.cokerToCokerComp g)) + finrank K (P ⧸ range g) := by
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  have : FiniteDimensional K (ker (g ∘ₗ f)) := Module.Finite.ker_comp f g
  refine ⟨?_, (f.kerCompToKer g).finrank_eq_finrank_range_add_finrank_range_of_exact _
    (f.exact_kerCompToKer_kerToCoker g),
    (f.kerToCoker g).finrank_eq_finrank_range_add_finrank_range_of_exact _
      (f.exact_kerToCoker_cokerToCokerComp g), ?_⟩
  · rw [LinearMap.finrank_eq_finrank_range_add_finrank_range_of_exact _ _
      (f.exact_inclusion_kerCompToKer g),
      LinearMap.finrank_range_of_inj (Submodule.inclusion_injective (ker_le_ker_comp f g))]
  · rw [LinearMap.finrank_eq_finrank_range_add_finrank_range_of_exact _ _
      (f.exact_cokerToCokerComp_factor g),
      LinearMap.range_eq_top.2 (Submodule.factor_surjective _), finrank_top]

/-- The connecting map `ker (h ∘ g) → coker f` has rank that of `ker g → coker f` plus that of
its composite with `coker f → coker (g ∘ f)`. -/
private theorem finrank_range_kerToCoker_comp [FiniteDimensional K (N ⧸ range f)] :
    finrank K (range (f.kerToCoker (h ∘ₗ g))) = finrank K (range (f.kerToCoker g)) +
      finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) := by
  have hle : range (f.kerToCoker g) ≤ range (f.kerToCoker (h ∘ₗ g)) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨y, by simp [mem_ker.1 y.property]⟩, by rw [kerToCoker_apply, kerToCoker_apply]⟩
  have hr := finrank_range_add_finrank_ker
    ((f.cokerToCokerComp g).domRestrict (range (f.kerToCoker (h ∘ₗ g))))
  rw [range_domRestrict, ← range_comp, ker_domRestrict,
    (f.exact_kerToCoker_cokerToCokerComp g).linearMap_ker_eq,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hr
  omega

/-! ### Compatibilities between the four kernel–cokernel sequences -/

private theorem inclusion_comp_inclusion :
    ⇑(Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h)) ∘
        ⇑(Submodule.inclusion (ker_le_ker_comp f g)) =
      ⇑(Submodule.inclusion (ker_le_ker_comp f (h ∘ₗ g))) :=
  funext fun _ ↦ Subtype.ext (by simp)

private theorem kerCompToKer_comp_inclusion :
    ⇑(f.kerCompToKer (h ∘ₗ g)) ∘ ⇑(Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h)) =
      ⇑(Submodule.inclusion (ker_le_ker_comp g h)) ∘ ⇑(f.kerCompToKer g) :=
  funext fun _ ↦ Subtype.ext (by simp [coe_kerCompToKer_apply])

private theorem kerToCoker_comp_inclusion :
    ⇑(f.kerToCoker (h ∘ₗ g)) ∘ ⇑(Submodule.inclusion (ker_le_ker_comp g h)) =
      ⇑(f.kerToCoker g) :=
  funext fun _ ↦ by simp [kerToCoker_apply]

private theorem cokerToCokerComp_comp_cokerToCokerComp :
    ⇑((g ∘ₗ f).cokerToCokerComp h) ∘ ⇑(f.cokerToCokerComp g) =
      ⇑(f.cokerToCokerComp (h ∘ₗ g)) := by
  funext z
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [Function.comp_apply, cokerToCokerComp_mk, LinearMap.comp_apply]

private theorem kerCompToKer_comp_kerCompToKer :
    ⇑(g.kerCompToKer h) ∘ ⇑(f.kerCompToKer (h ∘ₗ g)) = ⇑((g ∘ₗ f).kerCompToKer h) :=
  funext fun _ ↦ Subtype.ext (by simp [coe_kerCompToKer_apply])

private theorem kerToCoker_comp_kerCompToKer :
    ⇑((g ∘ₗ f).kerToCoker h) ∘ ⇑(g.kerCompToKer h) =
      ⇑(f.cokerToCokerComp g) ∘ ⇑(f.kerToCoker (h ∘ₗ g)) :=
  funext fun _ ↦ by simp [kerToCoker_apply, coe_kerCompToKer_apply, cokerToCokerComp_mk]

private theorem factor_comp_kerToCoker :
    ⇑(Submodule.factor (range_comp_le_range f g)) ∘ ⇑((g ∘ₗ f).kerToCoker h) =
      ⇑(g.kerToCoker h) :=
  funext fun _ ↦ by simp [kerToCoker_apply]

private theorem factor_comp_cokerToCokerComp :
    ⇑(Submodule.factor (range_comp_le_range f (h ∘ₗ g))) ∘ ⇑((g ∘ₗ f).cokerToCokerComp h) =
      ⇑(g.cokerToCokerComp h) ∘ ⇑(Submodule.factor (range_comp_le_range f g)) := by
  funext z
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [Function.comp_apply, cokerToCokerComp_mk, Submodule.mapQ_apply, LinearMap.id_apply]

private theorem factor_comp_factor :
    ⇑(Submodule.factor (range_comp_le_range g h)) ∘
        ⇑(Submodule.factor (range_comp_le_range f (h ∘ₗ g))) =
      ⇑(Submodule.factor (range_comp_le_range (g ∘ₗ f) h)) := by
  funext z
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [Function.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply]

/-! ### Adapted families -/

/-- The kernel part of the adapted families: a basis of `ker f`, completed to bases of
`ker (g ∘ f)` and of `ker (h ∘ g ∘ f)`. -/
private theorem exists_linearIndependent_ker [FiniteDimensional K (ker f)]
    [FiniteDimensional K (ker g)]
    [FiniteDimensional K (ker h)] :
    ∃ (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
      (b : Fin (finrank K (range ((g ∘ₗ f).kerCompToKer h))) → ker (h ∘ₗ g ∘ₗ f)),
      LinearIndependent K (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v)
          b) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_comp (f.kerCompToKer g)
  obtain ⟨b, hb⟩ := exists_linearIndependent_comp ((g ∘ₗ f).kerCompToKer h)
  refine ⟨v, b, LinearIndependent.fin_append_of_linearIndependent_comp ?_ _
    (fun _ ↦ ((g ∘ₗ f).exact_inclusion_kerCompToKer h).apply_apply_eq_zero _) hb⟩
  refine LinearIndependent.map' (LinearIndependent.fin_append_of_linearIndependent_comp ?_ _
    (fun _ ↦ (f.exact_inclusion_kerCompToKer g).apply_apply_eq_zero _) hv) _
    (Submodule.ker_inclusion _ _ _)
  exact (Module.finBasis K _).linearIndependent.map' _ (Submodule.ker_inclusion _ _ _)

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] [FiniteDimensional K (ker h)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (P ⧸ range g)]
  [FiniteDimensional K (Q ⧸ range h)] [FiniteDimensional K (ker (h ∘ₗ g))]
  [FiniteDimensional K (Q ⧸ range (h ∘ₗ g))]

/-- Families of vectors adapted to the kernel–cokernel sequences of the four composites
`g ∘ f`, `h ∘ (g ∘ f)`, `(h ∘ g) ∘ f` and `h ∘ g`, with the linear independence statements that
make the exterior products built from them nonzero. -/
private structure AssocData where
  v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f)
  b : Fin (finrank K (range ((g ∘ₗ f).kerCompToKer h))) → ker (h ∘ₗ g ∘ₗ f)
  w : Fin (finrank K (range (f.kerToCoker g))) → ker g
  w₂ : Fin (finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g)))) → ker (h ∘ₗ g)
  x : Fin (finrank K (range (f.cokerToCokerComp (h ∘ₗ g)))) → N ⧸ range f
  c : Fin (finrank K (range (g.kerToCoker h))) → ker h
  y : Fin (finrank K (range (g.cokerToCokerComp h))) → P ⧸ range (g ∘ₗ f)
  e : Fin (finrank K (Q ⧸ range h)) → Q ⧸ range (h ∘ₗ g ∘ₗ f)
  li_ker : LinearIndependent K (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
    Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v) b)
  li_cokerf : LinearIndependent K
    (Fin.append (f.kerToCoker g ∘ w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ w₂) x))
  li_cokergf : LinearIndependent K (Fin.append
    (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ w₂) (f.cokerToCokerComp g ∘ x))
    (Fin.append ((g ∘ₗ f).kerToCoker h ∘ c) y))
  li_cokerg : LinearIndependent K
    (Fin.append (g.kerToCoker h ∘ c) (Submodule.factor (range_comp_le_range f g) ∘ y))
  li_cokerhg : LinearIndependent K (Fin.append
    (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ y)
    (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ e))
  li_cokerh : LinearIndependent K (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ e)

private theorem nonempty_assocData : Nonempty (AssocData f g h) := by
  have : FiniteDimensional K (Q ⧸ range ((h ∘ₗ g) ∘ₗ f)) :=
    Module.Finite.quotient_range_comp f (h ∘ₗ g)
  obtain ⟨v, b, hvb⟩ := exists_linearIndependent_ker f g h
  obtain ⟨w, hw⟩ := exists_linearIndependent_comp (f.kerToCoker g)
  obtain ⟨w₂, hw₂⟩ :=
    exists_linearIndependent_comp (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))
  rw [LinearMap.coe_comp] at hw₂
  obtain ⟨x, hx⟩ := exists_linearIndependent_comp (f.cokerToCokerComp (h ∘ₗ g))
  obtain ⟨c, hc⟩ := exists_linearIndependent_comp (g.kerToCoker h)
  obtain ⟨y', hy'⟩ := exists_linearIndependent_comp (g.cokerToCokerComp h)
  choose y hy using fun i ↦ Submodule.factor_surjective (range_comp_le_range f g) (y' i)
  obtain ⟨e, he⟩ := exists_linearIndependent_comp_of_surjective
    (Submodule.factor_surjective (range_comp_le_range (g ∘ₗ f) h))
  have hy₁ : ⇑(Submodule.factor (range_comp_le_range f g)) ∘ y = y' := funext hy
  -- In `coker (g ∘ f)`: the images of `w₂` and `x`, which lie in the image of `coker f`.
  have hin := hw₂.fin_append_of_linearIndependent_comp ((g ∘ₗ f).cokerToCokerComp h)
    (fun i ↦ by
      have := congrFun (cokerToCokerComp_comp_cokerToCokerComp f g h)
        (f.kerToCoker (h ∘ₗ g) (w₂ i))
      simp only [Function.comp_apply] at this ⊢
      rw [this]
      exact (f.exact_kerToCoker_cokerToCokerComp (h ∘ₗ g)).apply_apply_eq_zero _)
    (by rwa [← Function.comp_assoc, cokerToCokerComp_comp_cokerToCokerComp])
  -- In `coker g`: the images of `c` and of `y`.
  have hcg := hc.fin_append_of_linearIndependent_comp (g.cokerToCokerComp h)
    (y := ⇑(Submodule.factor (range_comp_le_range f g)) ∘ y)
    (fun _ ↦ (g.exact_kerToCoker_cokerToCokerComp h).apply_apply_eq_zero _) (by rwa [hy₁])
  refine ⟨⟨v, b, w, w₂, x, c, y, e, hvb, ?_, ?_, hcg, ?_, he⟩⟩
  · refine hw.fin_append_of_linearIndependent_comp (f.cokerToCokerComp g)
      (fun _ ↦ (f.exact_kerToCoker_cokerToCokerComp g).apply_apply_eq_zero _) ?_
    rwa [Fin.comp_append, ← Function.comp_assoc]
  · refine hin.fin_append_of_linearIndependent_comp
      (Submodule.factor (range_comp_le_range f g))
      (fun i ↦ ?_) ?_
    · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Function.comp_apply] <;>
        exact (f.exact_cokerToCokerComp_factor g).apply_apply_eq_zero _
    · rwa [Fin.comp_append, ← Function.comp_assoc, factor_comp_kerToCoker]
  · refine LinearIndependent.fin_append_of_linearIndependent_comp ?_
      (Submodule.factor (range_comp_le_range g h)) (fun i ↦ ?_) ?_
    · rwa [← Function.comp_assoc, factor_comp_cokerToCokerComp, Function.comp_assoc, hy₁]
    · have := congrFun (factor_comp_cokerToCokerComp f g h) (y i)
      simp only [Function.comp_apply] at this ⊢
      rw [this]
      exact (g.exact_cokerToCokerComp_factor h).apply_apply_eq_zero _
    · rwa [← Function.comp_assoc, factor_comp_factor]

/-- The dimension counts relating the four kernel–cokernel sequences. -/
private theorem finrank_assoc :
    finrank K (range ((g ∘ₗ f).kerToCoker h)) =
        finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) +
          finrank K (range (g.kerToCoker h)) ∧
      finrank K (range ((g ∘ₗ f).cokerToCokerComp h)) =
        finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) +
          finrank K (range (g.cokerToCokerComp h)) ∧
      finrank K (range (f.cokerToCokerComp g)) =
        finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) +
          finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) ∧
      finrank K (range (f.kerCompToKer (h ∘ₗ g))) =
        finrank K (range (f.kerCompToKer g)) + finrank K (range ((g ∘ₗ f).kerCompToKer h)) ∧
      finrank K (range (g.kerCompToKer h)) =
        finrank K (range ((g ∘ₗ f).kerCompToKer h)) +
          finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) := by
  have : FiniteDimensional K (ker (g ∘ₗ f)) := Module.Finite.ker_comp f g
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  obtain ⟨a₁, a₂, a₃, a₄⟩ := finrank_comp_sixTerm f g
  obtain ⟨b₁, b₂, b₃, b₄⟩ := finrank_comp_sixTerm (g ∘ₗ f) h
  obtain ⟨c₁, c₂, c₃, c₄⟩ := finrank_comp_sixTerm f (h ∘ₗ g)
  obtain ⟨d₁, d₂, d₃, d₄⟩ := finrank_comp_sixTerm g h
  have e := finrank_range_kerToCoker_comp f g h
  have : finrank K (ker ((h ∘ₗ g) ∘ₗ f)) = finrank K (ker (h ∘ₗ g ∘ₗ f)) := rfl
  omega

/-! ### Evaluating the two composites -/

/-- The composition law of `g ∘ f` on `α ⊗ ψ₀`: the second step of the left composite. -/
private theorem assoc_left_tmul₂ (d : AssocData f g h) {α : TauCeti.detLine K (ker (g ∘ₗ f))}
    (hα : (α : ExteriorAlgebra K (ker (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v))
    {γ₂ : TauCeti.detLine K (ker g)} (hγ₂ : (γ₂ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w))
    {δ₁ : TauCeti.detLine K (N ⧸ range f)} (hδ₁ : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (f.kerToCoker g ∘ d.w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x)))
    {ψ₁ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ₁ : ψ₁ δ₁ = 1)
    {δ₂ : TauCeti.detLine K (P ⧸ range g)} (hδ₂ : (δ₂ : ExteriorAlgebra K (P ⧸ range g)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (g.kerToCoker h ∘ d.c) (Submodule.factor (range_comp_le_range f g) ∘ d.y)))
    {ψ₂ : Dual K (TauCeti.detLine K (P ⧸ range g))} (hψ₂ : ψ₂ δ₂ = 1)
    {δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hδ₀ : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ d.w₂)
        (f.cokerToCokerComp g ∘ d.x)) (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y)))
    (ψ₀ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f)))) :
    f.detLineCompEquiv g (α ⊗ₜ ψ₀) = ψ₀ δ₀ •
      ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ ψ₁) ⊗ₜ (γ₂ ⊗ₜ ψ₂)) := by
  obtain ⟨-, -, d₃, -⟩ := finrank_comp_sixTerm g h
  obtain ⟨-, -, c₄, -, -⟩ := finrank_assoc f g h
  have hδ₁' : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerToCoker g ∘ d.w)
        (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x ∘ Fin.cast c₄)) := by
    rw [hδ₁]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  have hδ₀' : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.cokerToCokerComp g ∘
        (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x ∘ Fin.cast c₄))
        (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y ∘ Fin.cast d₃)) := by
    rw [hδ₀]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hδ₂' : exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘
      (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y ∘ Fin.cast d₃)) = δ₂ := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, hδ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, factor_comp_kerToCoker]
  rw [f.detLineCompEquiv_tmul g _ _ _ _ _ hα hγ₂ hδ₁' hδ₀' ψ₀ hψ₁ (by rw [hδ₂']; exact hψ₂)]

/-- The composition law of `(h ∘ g) ∘ f` on an exterior product `β ⊗ φ` built from adapted
families: the first step of the right composite. -/
private theorem assoc_right_tmul₁ (d : AssocData f g h) {β : TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f))}
    (hβ : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
        d.b))
    {β₂ : TauCeti.detLine K (ker (h ∘ₗ g))}
    (hβ₂ : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂)))
    {ε : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ Fin.append (f.cokerToCokerComp g ∘ d.x) d.y)
        d.e))
    {δ₁ : TauCeti.detLine K (N ⧸ range f)} (hδ₁ : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (f.kerToCoker g ∘ d.w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x)))
    {ψ₁ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ₁ : ψ₁ δ₁ = 1)
    {δ₃ : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g))}
    (hδ₃ : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ d.y)
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)))
    {χ₃ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g)))} (hχ₃ : χ₃ δ₃ = 1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    f.detLineCompEquiv (h ∘ₗ g) (β ⊗ₜ φ) = φ ε •
      ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ ψ₁) ⊗ₜ
        (((-1 : K) ^ (finrank K (range ((g ∘ₗ f).kerCompToKer h)) *
          finrank K (range (f.kerToCoker g))) • β₂) ⊗ₜ χ₃)) := by
  obtain ⟨-, -, -, d₄⟩ := finrank_comp_sixTerm g h
  obtain ⟨-, -, -, c₆, -⟩ := finrank_assoc f g h
  have c₇ := finrank_range_kerToCoker_comp f g h
  have hβ' : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f (h ∘ₗ g)) ∘ Module.finBasis K (ker f))
        (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ d.v) d.b ∘
          Fin.cast c₆)) := by
    rw [hβ]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, inclusion_comp_inclusion]
  -- `β₂` lists the images of `v`, `w`, `b` and `w₂`; the composition law wants `v`, `b`, `w`, `w₂`.
  have hβ₂' : ((((-1 : K) ^ (finrank K (range ((g ∘ₗ f).kerCompToKer h)) *
      finrank K (range (f.kerToCoker g)))) • β₂ : TauCeti.detLine K (ker (h ∘ₗ g))) :
        ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ (Fin.append
        (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ d.v) d.b ∘ Fin.cast c₆))
        (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘ d.w) d.w₂ ∘ Fin.cast c₇)) := by
    rw [Submodule.coe_smul, hβ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc,
      kerCompToKer_comp_inclusion]
    rw [ιMulti_mul_ιMulti_mul_swap (b := finrank K (range ((g ∘ₗ f).kerCompToKer h)))]
  have hδ₁' : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerToCoker (h ∘ₗ g) ∘
        (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘ d.w) d.w₂ ∘ Fin.cast c₇))
        d.x) := by
    rw [hδ₁]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc,
      kerToCoker_comp_inclusion]
  have hε' : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.cokerToCokerComp (h ∘ₗ g) ∘ d.x)
        (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ d.y) d.e ∘ Fin.cast d₄)) := by
    rw [hε]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc,
      cokerToCokerComp_comp_cokerToCokerComp]
  have hδ₃' : exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ d.y) d.e ∘ Fin.cast d₄)) = δ₃ := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, hδ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  rw [f.detLineCompEquiv_tmul (h ∘ₗ g) _ _ _ _ _ hβ' hβ₂' hδ₁' hε' φ hψ₁
    (by rw [hδ₃']; exact hχ₃)]

/-- The composition law of `h ∘ g` on `β₂ ⊗ χ₃`: the second step of the right composite. -/
private theorem assoc_right_tmul₂ (d : AssocData f g h) {β₂ : TauCeti.detLine K (ker (h ∘ₗ g))}
    (hβ₂ : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂)))
    {γ₂ : TauCeti.detLine K (ker g)} (hγ₂ : (γ₂ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w))
    {γ₃ : TauCeti.detLine K (ker h)} (hγ₃ : (γ₃ : ExteriorAlgebra K (ker h)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c)))
    {δ₂ : TauCeti.detLine K (P ⧸ range g)} (hδ₂ : (δ₂ : ExteriorAlgebra K (P ⧸ range g)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (g.kerToCoker h ∘ d.c) (Submodule.factor (range_comp_le_range f g) ∘ d.y)))
    {ψ₂ : Dual K (TauCeti.detLine K (P ⧸ range g))} (hψ₂ : ψ₂ δ₂ = 1)
    {δ₃ : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g))}
    (hδ₃ : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ d.y)
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)))
    (χ₃ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g))))
    {χ : Dual K (TauCeti.detLine K (Q ⧸ range h))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ d.e)) =
      1) :
    g.detLineCompEquiv h (β₂ ⊗ₜ χ₃) = χ₃ δ₃ • ((γ₂ ⊗ₜ ψ₂) ⊗ₜ (γ₃ ⊗ₜ χ)) := by
  obtain ⟨-, a₂, -, -⟩ := finrank_comp_sixTerm f g
  obtain ⟨-, -, -, -, c₁₀⟩ := finrank_assoc f g h
  have hβ₂' : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        (Fin.append (f.kerCompToKer g ∘ d.v) d.w ∘ Fin.cast a₂))
        (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂ ∘ Fin.cast c₁₀)) := by
    rw [hβ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hγ₃' : (γ₃ : ExteriorAlgebra K (ker h)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (g.kerCompToKer h ∘
        (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂ ∘ Fin.cast c₁₀)) d.c) := by
    rw [hγ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc,
      kerCompToKer_comp_kerCompToKer]
  have hδ₃' : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (g.cokerToCokerComp h ∘ (Submodule.factor (range_comp_le_range f g) ∘ d.y))
        (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)) := by
    rw [hδ₃]
    simp only [← Function.comp_assoc, factor_comp_cokerToCokerComp]
  have hγ₂' : exteriorPower.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w ∘ Fin.cast a₂) =
      γ₂ :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      hγ₂])
  rw [g.detLineCompEquiv_tmul h _ _ _ _ _ hβ₂' hγ₃' hδ₂ hδ₃' χ₃ hψ₂
      (by rw [← Function.comp_assoc, factor_comp_factor]; exact hχ), hγ₂']

/-- The right composite `det ((h ∘ g) ∘ f) → det f ⊗ det (h ∘ g) → det f ⊗ (det g ⊗ det h)` on an
exterior product `β ⊗ φ` built from adapted families. -/
private theorem assoc_right_tmul (d : AssocData f g h) {β : TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f))}
    (hβ : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
        d.b))
    {γ₂ : TauCeti.detLine K (ker g)} (hγ₂ : (γ₂ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w))
    {γ₃ : TauCeti.detLine K (ker h)} (hγ₃ : (γ₃ : ExteriorAlgebra K (ker h)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c)))
    {ε : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ Fin.append (f.cokerToCokerComp g ∘ d.x) d.y)
        d.e))
    {δ₁ : TauCeti.detLine K (N ⧸ range f)} (hδ₁ : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (f.kerToCoker g ∘ d.w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x)))
    {ψ₁ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ₁ : ψ₁ δ₁ = 1)
    {δ₂ : TauCeti.detLine K (P ⧸ range g)} (hδ₂ : (δ₂ : ExteriorAlgebra K (P ⧸ range g)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (g.kerToCoker h ∘ d.c) (Submodule.factor (range_comp_le_range f g) ∘ d.y)))
    {ψ₂ : Dual K (TauCeti.detLine K (P ⧸ range g))} (hψ₂ : ψ₂ δ₂ = 1)
    {χ : Dual K (TauCeti.detLine K (Q ⧸ range h))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ d.e)) =
      1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    (g.detLineCompEquiv h).lTensor f.detLine (f.detLineCompEquiv (h ∘ₗ g) (β ⊗ₜ φ)) =
      (φ ε * (-1) ^ (finrank K (range (f.kerToCoker g)) *
          finrank K (range ((g ∘ₗ f).kerCompToKer h)))) •
        ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ ψ₁) ⊗ₜ
          ((γ₂ ⊗ₜ ψ₂) ⊗ₜ (γ₃ ⊗ₜ χ))) := by
  obtain ⟨-, a₂, -, -⟩ := finrank_comp_sixTerm f g
  obtain ⟨d₁, -, -, d₄⟩ := finrank_comp_sixTerm g h
  obtain ⟨-, -, -, -, c₁₀⟩ := finrank_assoc f g h
  obtain ⟨δ₃, χ₃, hδ₃, hχ₃⟩ := exists_detLine_coe_eq d₄ d.li_cokerhg
  obtain ⟨β₂, hβ₂⟩ := exists_detLine_coe_eq_ιMulti (K := K) (V := ker (h ∘ₗ g)) (by omega)
    (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
      Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂))
  rw [assoc_right_tmul₁ f g h d hβ hβ₂ hε hδ₁ hψ₁ hδ₃ hχ₃ φ, map_smul, LinearEquiv.lTensor_tmul,
    ← TensorProduct.smul_tmul', map_smul,
    assoc_right_tmul₂ f g h d hβ₂ hγ₂ hγ₃ hδ₂ hψ₂ hδ₃ χ₃ hχ, hχ₃, one_smul,
    TensorProduct.tmul_smul, smul_smul, mul_comm (finrank K (range (f.kerToCoker g)))]

variable [FiniteDimensional K (ker (g ∘ₗ f))] [FiniteDimensional K (P ⧸ range (g ∘ₗ f))]

/-- The composition law of `h ∘ (g ∘ f)` on an exterior product `β ⊗ φ` built from adapted
families: the first step of the left composite. -/
private theorem assoc_left_tmul₁ (d : AssocData f g h) {β : TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f))}
    (hβ : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
        d.b))
    {α : TauCeti.detLine K (ker (g ∘ₗ f))}
    (hα : (α : ExteriorAlgebra K (ker (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v))
    {γ₃ : TauCeti.detLine K (ker h)} (hγ₃ : (γ₃ : ExteriorAlgebra K (ker h)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c)))
    {ε : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ Fin.append (f.cokerToCokerComp g ∘ d.x) d.y)
        d.e))
    {δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hδ₀ : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ d.w₂)
        (f.cokerToCokerComp g ∘ d.x)) (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y)))
    {ψ₀ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f)))} (hψ₀ : ψ₀ δ₀ = 1)
    {χ : Dual K (TauCeti.detLine K (Q ⧸ range h))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ d.e)) =
      1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    (g ∘ₗ f).detLineCompEquiv h (β ⊗ₜ φ) =
      φ ε • ((α ⊗ₜ ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
        finrank K (range (g.kerToCoker h))) • ψ₀)) ⊗ₜ (γ₃ ⊗ₜ χ)) := by
  obtain ⟨a₁, -, -, -⟩ := finrank_comp_sixTerm f g
  obtain ⟨c₂, c₃, -, -, -⟩ := finrank_assoc f g h
  have hβ' : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ (Fin.append
        (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v ∘
          Fin.cast a₁)) d.b) := by
    rw [hβ]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hγ₃' : (γ₃ : ExteriorAlgebra K (ker h)) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c ∘ Fin.cast c₂)) := by
    rw [hγ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  -- `δ₀` lists the images of `w₂`, `x`, `c` and `y`; the composition law wants `w₂`, `c`, `x`, `y`.
  have hδ₀' : ((((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h)))) • δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))) :
        ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).kerToCoker h ∘ (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c ∘
        Fin.cast c₂)) (Fin.append (f.cokerToCokerComp g ∘ d.x) d.y ∘ Fin.cast c₃)) := by
    rw [Submodule.coe_smul, hδ₀]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc,
      kerToCoker_comp_kerCompToKer]
    rw [ιMulti_mul_ιMulti_mul_swap, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
      one_smul]
  have hε' : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘
        (Fin.append (f.cokerToCokerComp g ∘ d.x) d.y ∘ Fin.cast c₃)) d.e) := by
    rw [hε]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hψ₀' : ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h))) • ψ₀)
        ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
          finrank K (range (g.kerToCoker h))) • δ₀) = 1 := by
    rw [LinearMap.smul_apply, map_smul, hψ₀, smul_eq_mul, smul_eq_mul, mul_one, ← mul_pow,
      neg_one_mul, neg_neg, one_pow]
  have hα' : exteriorPower.ιMulti K _ (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘
      Module.finBasis K (ker f)) d.v ∘ Fin.cast a₁) = α :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      hα])
  rw [(g ∘ₗ f).detLineCompEquiv_tmul h _ _ _ _ _ hβ' hγ₃' hδ₀' hε' φ hψ₀' hχ, hα']

/-- The left composite `det (h ∘ g ∘ f) → det (g ∘ f) ⊗ det h → (det f ⊗ det g) ⊗ det h`, followed
by the associator, on an exterior product `β ⊗ φ` built from adapted families. -/
private theorem assoc_left_tmul (d : AssocData f g h) {β : TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f))}
    (hβ : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
        d.b))
    {γ₂ : TauCeti.detLine K (ker g)} (hγ₂ : (γ₂ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w))
    {γ₃ : TauCeti.detLine K (ker h)} (hγ₃ : (γ₃ : ExteriorAlgebra K (ker h)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c)))
    {ε : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ Fin.append (f.cokerToCokerComp g ∘ d.x) d.y)
        d.e))
    {δ₁ : TauCeti.detLine K (N ⧸ range f)} (hδ₁ : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (f.kerToCoker g ∘ d.w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x)))
    {ψ₁ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ₁ : ψ₁ δ₁ = 1)
    {δ₂ : TauCeti.detLine K (P ⧸ range g)} (hδ₂ : (δ₂ : ExteriorAlgebra K (P ⧸ range g)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (g.kerToCoker h ∘ d.c) (Submodule.factor (range_comp_le_range f g) ∘ d.y)))
    {ψ₂ : Dual K (TauCeti.detLine K (P ⧸ range g))} (hψ₂ : ψ₂ δ₂ = 1)
    {χ : Dual K (TauCeti.detLine K (Q ⧸ range h))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ d.e)) =
      1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    TensorProduct.assoc K _ _ _
        ((f.detLineCompEquiv g).rTensor h.detLine ((g ∘ₗ f).detLineCompEquiv h (β ⊗ₜ φ))) =
      (φ ε * (-1) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
          finrank K (range (g.kerToCoker h)))) •
        ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ ψ₁) ⊗ₜ
          ((γ₂ ⊗ₜ ψ₂) ⊗ₜ (γ₃ ⊗ₜ χ))) := by
  obtain ⟨a₁, -, -, -⟩ := finrank_comp_sixTerm f g
  obtain ⟨-, -, b₃, -⟩ := finrank_comp_sixTerm (g ∘ₗ f) h
  obtain ⟨c₂, c₃, -, -, -⟩ := finrank_assoc f g h
  obtain ⟨δ₀, ψ₀, hδ₀, hψ₀⟩ := exists_detLine_coe_eq (by omega) d.li_cokergf
  obtain ⟨α, hα⟩ := exists_detLine_coe_eq_ιMulti (K := K) (V := ker (g ∘ₗ f)) a₁
    (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
  rw [assoc_left_tmul₁ f g h d hβ hα hγ₃ hε hδ₀ hψ₀ hχ φ, map_smul, LinearEquiv.rTensor_tmul,
    assoc_left_tmul₂ f g h d hα hγ₂ hδ₁ hψ₁ hδ₂ hψ₂ hδ₀]
  simp only [map_smul, ← TensorProduct.smul_tmul', TensorProduct.assoc_tmul, LinearMap.smul_apply,
    hψ₀, smul_smul, smul_eq_mul, mul_one]

/-! ### Associativity -/

/-- **Associativity of the composition law of determinant lines.** For linear maps
`f : M → N`, `g : N → P` and `h : P → Q` with finite-dimensional kernels and cokernels, the two
ways of splitting `det (h ∘ g ∘ f)` with the composition law (`LinearMap.detLineCompEquiv`), first
off `h` and then off `f`, or first off `f` and then off `h`, agree up to the Koszul sign
`(-1) ^ (r₁ r₂ + r₃ r₄)`. Here `r₁` and `r₂` are the ranks of the connecting map
`ker g → coker f` and of `ker (h ∘ g ∘ f) → ker h`, and `r₃` and `r₄` those of
`coker f → coker (h ∘ g ∘ f)` and of the connecting map `ker h → coker g`.

The sign can be nontrivial. For `f : K → K²` the first inclusion, `g` the projection of `K²` onto
the first coordinate line and `h : K² → K` the second coordinate, `r₁ = r₂ = 1` and `r₃ = 0`, so
the two isomorphisms differ by `-1`, which is not `1` unless `K` has characteristic two.

The composite maps `g ∘ f` and `h ∘ g` need finite-dimensional kernels and cokernels for their
composition laws to be defined; these hold automatically (`Module.Finite.ker_comp`,
`Module.Finite.quotient_range_comp`). -/
theorem detLineCompEquiv_assoc (x : (h ∘ₗ g ∘ₗ f).detLine) :
    TensorProduct.assoc K _ _ _
        ((f.detLineCompEquiv g).rTensor h.detLine ((g ∘ₗ f).detLineCompEquiv h x)) =
      (-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
          finrank K (range ((g ∘ₗ f).kerCompToKer h)) +
        finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) * finrank K (range (g.kerToCoker h))) •
        (g.detLineCompEquiv h).lTensor f.detLine (f.detLineCompEquiv (h ∘ₗ g) x) := by
  have : FiniteDimensional K (ker (h ∘ₗ g ∘ₗ f)) := Module.Finite.ker_comp (g ∘ₗ f) h
  obtain ⟨d⟩ := nonempty_assocData f g h
  obtain ⟨a₁, a₂, a₃, -⟩ := finrank_comp_sixTerm f g
  obtain ⟨b₁, b₂, -, b₄⟩ := finrank_comp_sixTerm (g ∘ₗ f) h
  obtain ⟨-, -, d₃, -⟩ := finrank_comp_sixTerm g h
  obtain ⟨c₂, c₃, c₄, -, -⟩ := finrank_assoc f g h
  obtain ⟨β, η, hβ, hη⟩ := exists_detLine_coe_eq (by omega) d.li_ker
  obtain ⟨γ₂, hγ₂⟩ := exists_detLine_coe_eq_ιMulti (K := K) (V := ker g) (by omega)
    (Fin.append (f.kerCompToKer g ∘ d.v) d.w)
  obtain ⟨γ₃, hγ₃⟩ := exists_detLine_coe_eq_ιMulti (K := K) (V := ker h) (by omega)
    (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b) (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c))
  obtain ⟨ε, hε⟩ := exists_detLine_coe_eq_ιMulti (K := K) (V := Q ⧸ range (h ∘ₗ g ∘ₗ f))
    (by omega) (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘
      Fin.append (f.cokerToCokerComp g ∘ d.x) d.y) d.e)
  obtain ⟨δ₁, ψ₁, hδ₁, hψ₁⟩ := exists_detLine_coe_eq (by omega) d.li_cokerf
  obtain ⟨δ₂, ψ₂, hδ₂, hψ₂⟩ := exists_detLine_coe_eq d₃ d.li_cokerg
  obtain ⟨χ, hχ⟩ :=
    Projective.exists_dual_eq_one K ((exteriorPower.ιMulti_ne_zero_iff _).2 d.li_cokerh)
  -- Both sides are linear in `x`; by `η z • β = z`, it suffices to compare them on `β ⊗ φ`.
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  | tmul z φ =>
    rw [← Module.Invertible.apply_smul_eq_self hη z, ← TensorProduct.smul_tmul', map_smul,
      map_smul, map_smul, map_smul, map_smul, assoc_left_tmul f g h d hβ hγ₂ hγ₃ hε hδ₁ hψ₁ hδ₂
      hψ₂ hχ φ, assoc_right_tmul f g h d hβ hγ₂ hγ₃ hε hδ₁ hψ₁ hδ₂ hψ₂ hχ φ, smul_smul,
      smul_smul, smul_smul]
    congr 1
    have hsq : ((-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
        finrank K (range ((g ∘ₗ f).kerCompToKer h)))) * (-1) ^ (finrank K
          (range (f.kerToCoker g)) * finrank K (range ((g ∘ₗ f).kerCompToKer h))) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [pow_add]
    linear_combination (-(η z * φ ε * (-1) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h))))) * hsq

end Assoc

end LinearMap
