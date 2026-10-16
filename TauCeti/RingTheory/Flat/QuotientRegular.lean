/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Flat.Extensions

/-!
# Flat quotients by universally regular elements

Let `B` be a flat algebra over a commutative ring `R` and `g ∈ B`. If multiplication by `g` on
`(R ⧸ I) ⊗[R] B` is injective for every finitely generated ideal `I` of `R`, then `B ⧸ (g)` is a
flat `R`-module.

Conversely, if `g` is a nonzerodivisor on `B` and `B ⧸ (g)` is flat over `R`, then `g` stays a
nonzerodivisor after every base change. Thus, when `B` itself is flat over `R` and `g` is a
nonzerodivisor on `B`, flatness of the quotient is equivalent to universal regularity of `g`.
This is the algebraic criterion that makes a relative effective Cartier divisor remain an
effective Cartier divisor after arbitrary base change.

This is the claim inside Wedhorn's proof of Lemma 8.31(2): for `B = A⟨X⟩` over a complete
noetherian Tate ring `A`, and `g = f - X` or `g = 1 - f X`, the quotient is flat because
multiplication by `g` is injective on `M⟨X⟩ = M ⊗[A] A⟨X⟩` for every finitely generated `M` —
in particular for every `M = A ⧸ I`, which is all the argument uses. Wedhorn proves the claim
with the long exact `Tor` sequence. What the sequence encodes is a diagram chase, and that chase
is what is carried out here, against Mathlib's ideal criterion for flatness: `B ⧸ (g)` is flat
once `I ⊗[R] (B ⧸ (g)) → R ⊗[R] (B ⧸ (g))` is injective for every finitely generated ideal `I`.

## Main results

* `Module.Flat.quotient_span_singleton_of_lTensor_mulLeft_injective`: the statement above.
* `Module.Flat.lTensor_mulLeft_injective_of_quotient_span_singleton`: flatness of `B ⧸ (g)`
  makes multiplication by a regular `g` stay injective after tensoring with any module.
* `Module.Flat.isSMulRegular_one_tmul_of_quotient_span_singleton`: after any algebra base change
  `R → S`, assuming only a semiring structure on `S`, `1 ⊗ g` is a nonzerodivisor on `S ⊗[R] B`.
* `Module.Flat.quotient_span_singleton_iff_forall_lTensor_mulLeft_injective`: for a flat
  `R`-algebra `B` and a nonzerodivisor `g` on `B`, flatness of `B ⧸ (g)` is equivalent to
  injectivity after tensoring with every `R`-module.
* `Module.Flat.quotient_span_singleton_iff_forall_isSMulRegular_one_tmul`: for a flat
  `R`-algebra `B` and a nonzerodivisor `g` on `B`, flatness of `B ⧸ (g)` is equivalent to this
  universal regularity.

## Implementation notes

The forward implication asks only about `(R ⧸ I) ⊗[R] B` for finitely generated ideals `I`,
which is exactly what the chase consumes; a hypothesis on every finitely generated module, as
Wedhorn states it, specialises to this. The converse applies the standard fact that tensoring a
short exact sequence whose cokernel is flat preserves injectivity. Statements use the coefficient
module on the left, matching the orientation of Mathlib's flatness API.

The equivalences allow test modules and algebras in any universe at least that of `R`.
Their reverse implications test universe lifts of the quotients `R ⧸ I`.

The chase, for a finitely generated ideal `I`: an element of `I ⊗ (B ⧸ (g))` killed in
`R ⊗ (B ⧸ (g))` lifts to `I ⊗ B`, is there the image of `g` times some `w` in `R ⊗ B`, and
injectivity of `g` on `(R ⧸ I) ⊗ B` shows that `w` comes from `I ⊗ B`, so the element is `g`
times an element of `I ⊗ B` and dies in `I ⊗ (B ⧸ (g))`. Flatness of `B` enters twice: as
exactness of `I ⊗ B → R ⊗ B → (R ⧸ I) ⊗ B`, and as injectivity of `I ⊗ B → R ⊗ B`.

The product criterion `TauCeti.flat_quotient_span_singleton_mul` applies flatness of extensions to
sums of relative effective Cartier divisors: if `B ⧸ (a)` and `B ⧸ (b)` are flat over `R` and `b`
is a nonzerodivisor, then `B ⧸ (a * b)` is flat over `R`. Neither flatness of `B` nor regularity of
`a` is required.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 8.31.
-/

public section

open TensorProduct

namespace Module.Flat

universe u v w

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-! ### A flat quotient gives universal regularity -/

/-- If `g` is a nonzerodivisor on `B` and `B ⧸ (g)` is flat over `R`, multiplication by `g`
remains injective after tensoring `B` with any `R`-module. This is the short exact sequence
`0 → B → B → B ⧸ (g) → 0` tensored with that module. -/
theorem lTensor_mulLeft_injective_of_quotient_span_singleton {g : B}
    (hg : IsSMulRegular B g) [Flat R (B ⧸ Ideal.span {g})]
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Injective (LinearMap.lTensor M (LinearMap.mulLeft R g)) := by
  let π : B →ₗ[R] B ⧸ Ideal.span {g} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {g})).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hexact : Function.Exact (LinearMap.mulLeft R g) π := fun y ↦ by
    simp [π, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', mul_comm]
  exact LinearMap.lTensor_injective_of_exact_of_flat π hπ (LinearMap.mulLeft R g) hg
    hexact M

/-- If `g` is a nonzerodivisor on `B` and `B ⧸ (g)` is flat over `R`, then `1 ⊗ g` is a
nonzerodivisor after every algebra base change `R → S`. Only a semiring structure on `S` is
required; no commutativity or flatness assumption on `S` is needed. -/
theorem isSMulRegular_one_tmul_of_quotient_span_singleton {g : B}
    (hg : IsSMulRegular B g) [Flat R (B ⧸ Ideal.span {g})]
    (S : Type w) [Semiring S] [Algebra R S] :
    IsSMulRegular (S ⊗[R] B) ((1 : S) ⊗ₜ[R] g) := by
  let _ : AddCommGroup S := Module.addCommMonoidToAddCommGroup R
  simpa only [IsSMulRegular, smul_eq_mul, ← LinearMap.mulLeft_apply (R := R),
    LinearMap.mulLeft_tmul, LinearMap.mulLeft_one, ← LinearMap.lTensor_def] using
    lTensor_mulLeft_injective_of_quotient_span_singleton (R := R) hg S

/-! ### Universal regularity gives a flat quotient -/

/-- **A flat algebra modulo an element acting injectively on each `(R ⧸ I) ⊗[R] B` is flat.**
Let `B` be a flat `R`-algebra and `g ∈ B`. If `id ⊗ (g • ·) : (R ⧸ I) ⊗[R] B → (R ⧸ I) ⊗[R] B` is
injective for every finitely generated ideal `I`, then `B ⧸ (g)` is a flat `R`-module. This is the
`Tor`-sequence step of Wedhorn's Lemma 8.31(2); a consumer holding injectivity for every finitely
generated module, as Wedhorn states it, passes it at `M = R ⧸ I`. -/
theorem quotient_span_singleton_of_lTensor_mulLeft_injective [Flat R B] (g : B)
    (hg : ∀ ⦃I : Ideal R⦄, I.FG →
      Function.Injective (LinearMap.lTensor (R ⧸ I) (LinearMap.mulLeft R g))) :
    Flat R (B ⧸ Ideal.span {g}) := by
  rw [iff_rTensor_injective]
  intro I hI
  let v : B →ₗ[R] B := LinearMap.mulLeft R g
  let π : B →ₗ[R] B ⧸ Ideal.span {g} := (Ideal.Quotient.mkₐ R (Ideal.span {g})).toLinearMap
  have hexact : Function.Exact v π := fun y ↦ by
    simp [v, π, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', mul_comm]
  have hπv : π ∘ₗ v = 0 := hexact.linearMap_comp_eq_zero
  have hqι : I.mkQ ∘ₗ I.subtype = 0 := (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨z', rfl⟩ := LinearMap.lTensor_surjective I (g := π) Ideal.Quotient.mk_surjective z
  -- `rTensor B I.subtype z'` is killed by `lTensor R π`, so it is `g` times some `w`.
  have h1 : LinearMap.lTensor R π (LinearMap.rTensor B I.subtype z') = 0 := by
    simpa only [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor] using hz
  obtain ⟨w, hw⟩ := ((lTensor_exact R hexact) _).mp h1
  -- The image of `w` in `(R ⧸ I) ⊗ B` is killed by `g`, hence zero, so `w` comes from `I ⊗ B`.
  have h2 : LinearMap.lTensor (R ⧸ I) v (LinearMap.rTensor B I.mkQ w) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hw, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hqι,
      LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨z₀, hz₀⟩ := ((rTensor_exact B (LinearMap.exact_subtype_mkQ I)) _).mp
    ((injective_iff_map_eq_zero _).mp (hg hI) _ h2)
  -- Flatness of `B` makes `I ⊗ B → R ⊗ B` injective, so `z' = g • z₀`.
  have h4 : LinearMap.lTensor I v z₀ = z' :=
    rTensor_preserves_injective_linearMap I.subtype I.injective_subtype <| by
      simpa only [← hz₀, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor] using hw
  rw [← h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπv, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

/-- For a flat `R`-algebra `B` and a nonzerodivisor `g`, the quotient `B ⧸ (g)` is flat over `R`
if and only if multiplication by `g` remains injective after tensoring with every `R`-module. -/
theorem quotient_span_singleton_iff_forall_lTensor_mulLeft_injective [Flat R B] (g : B)
    (hg : IsSMulRegular B g) :
    Flat R (B ⧸ Ideal.span {g}) ↔
      ∀ (M : Type (max u w)) [AddCommGroup M] [Module R M],
        Function.Injective (LinearMap.lTensor M (LinearMap.mulLeft R g)) := by
  constructor
  · intro h M _ _
    let _ : Flat R (B ⧸ Ideal.span {g}) := h
    exact lTensor_mulLeft_injective_of_quotient_span_singleton hg M
  · intro h
    apply quotient_span_singleton_of_lTensor_mulLeft_injective g
    intro I _
    let e := (ULift.moduleEquiv : ULift.{w} (R ⧸ I) ≃ₗ[R] (R ⧸ I)).rTensor B
    rw [← EquivLike.injective_comp e]
    simpa only [e, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, LinearEquiv.coe_rTensor,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor] using
      e.injective.comp (h (ULift.{w} (R ⧸ I)))

/-- **Flatness of a quotient by a nonzerodivisor is equivalent to universal regularity.**
If `B` is flat over `R` and `g` is a nonzerodivisor on `B`, then `B ⧸ (g)` is flat over `R`
exactly when `1 ⊗ g` is a nonzerodivisor on `S ⊗[R] B` for every semiring `R`-algebra `S`,
including noncommutative algebras. -/
theorem quotient_span_singleton_iff_forall_isSMulRegular_one_tmul [Flat R B] (g : B)
    (hg : IsSMulRegular B g) :
    Flat R (B ⧸ Ideal.span {g}) ↔
      ∀ (S : Type (max u w)) [Semiring S] [Algebra R S],
        IsSMulRegular (S ⊗[R] B) ((1 : S) ⊗ₜ[R] g) := by
  constructor
  · intro h S _ _
    let _ : Flat R (B ⧸ Ideal.span {g}) := h
    exact isSMulRegular_one_tmul_of_quotient_span_singleton hg S
  · intro h
    apply quotient_span_singleton_of_lTensor_mulLeft_injective g
    intro I _
    let e : ULift.{w} (R ⧸ I) ⊗[R] B ≃ₐ[R] (R ⧸ I) ⊗[R] B :=
      Algebra.TensorProduct.congr ULift.algEquiv (AlgEquiv.refl : B ≃ₐ[R] B)
    have hregular : IsSMulRegular ((R ⧸ I) ⊗[R] B) ((1 : R ⧸ I) ⊗ₜ[R] g) :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv)
        (r := (1 : ULift.{w} (R ⧸ I)) ⊗ₜ[R] g) fun x ↦ by
          simp [e, smul_eq_mul]).mp (h (ULift.{w} (R ⧸ I)))
    simpa only [IsSMulRegular, smul_eq_mul, ← LinearMap.mulLeft_apply (R := R),
      LinearMap.mulLeft_tmul, LinearMap.mulLeft_one, ← LinearMap.lTensor_def] using hregular

end Module.Flat

namespace TauCeti

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- If `B ⧸ (a)` and `B ⧸ (b)` are flat over `R` and `b` is a nonzerodivisor on `B`, then
`B ⧸ (a * b)` is flat over `R`. Geometrically, this gives closure of relative effective Cartier
divisors under sums over an arbitrary base, without flatness of the ambient scheme. -/
theorem flat_quotient_span_singleton_mul {a b : B} (hb : IsSMulRegular B b)
    [Module.Flat R (B ⧸ Ideal.span {a})] [Module.Flat R (B ⧸ Ideal.span {b})] :
    Module.Flat R (B ⧸ Ideal.span {a * b}) := by
  -- Multiplication by `b` and the quotient map give `0 → B/(a) → B/(a*b) → B/(b) → 0`.
  have hab : Ideal.span {a * b} ≤ Ideal.span {b} := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨a, mul_comm _ _⟩
  have hi : Ideal.span {a} ≤ Submodule.comap (LinearMap.mulLeft B b) (Ideal.span {a * b}) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨c, by simp [mul_comm, mul_left_comm]⟩
  let i := (Submodule.mapQ (Ideal.span {a}) (Ideal.span {a * b})
    (LinearMap.mulLeft B b) hi).restrictScalars R
  let j := (Ideal.Quotient.factorₐ R hab).toLinearMap
  have hi_apply (x : B) : i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := by
    simpa only [i, LinearMap.restrictScalars_apply, Ideal.Quotient.mk_eq_mk,
      LinearMap.mulLeft_apply] using
      (Submodule.mapQ_apply (Ideal.span {a}) (Ideal.span {a * b}) (LinearMap.mulLeft B b)
        (h := hi) x)
  have hinj : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hi_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    have heq : b * (c * a) = b * x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨c, hb heq⟩)
  have hexact : Function.Exact i j := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [j, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact ⟨Ideal.Quotient.mk _ c, by simp only [hi_apply, mul_comm]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h := congrArg j hy
      rw [hi_apply] at h
      simpa [j, ← Ideal.Quotient.eq_zero_iff_mem] using h.symm
  exact hexact.flat_of_injective_of_surjective hinj (Ideal.Quotient.factor_surjective hab)

end TauCeti
