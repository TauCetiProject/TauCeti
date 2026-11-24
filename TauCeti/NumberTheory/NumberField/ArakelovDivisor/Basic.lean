/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Norm
public import TauCeti.NumberTheory.NumberField.Units.Log.Hyperplane
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Arakelov divisors on the ring of integers of a number field

An *Arakelov divisor* of a number field `K` is a formal sum
`D = Σ_𝔭 n_𝔭 [𝔭] + Σ_v λ_v [v]`, with integers `n_𝔭`, almost all zero, at the nonzero primes `𝔭`
of `𝓞 K`, and real numbers `λ_v` at the infinite places `v`. We record the finite part as the
invertible fractional ideal `𝔞 = ∏ 𝔭 ^ n_𝔭`, so an Arakelov divisor is a pair `(𝔞, λ)` and the
group law is componentwise. Its *degree* is
`deg^(𝔞, λ) = log N(𝔞) + Σ_v λ_v`,
and the *principal divisor* of `f ∈ Kˣ` is
`(f) = (f 𝓞 K, v ↦ -mult(v) log |f|_v)`.
The product formula says that principal divisors have degree zero, so the degree descends to the
*compactified Picard group* `Div^(𝓞 K) / {principal divisors}`.

The compactified Picard group is an extension of the ideal class group by the archimedean
divisors modulo units: forgetting the archimedean coefficients is a surjection onto
`ClassGroup (𝓞 K)` whose kernel is the image of the divisors `(𝓞 K, λ)` supported at infinity, and
such a divisor is principal exactly when `λ` is the weighted logarithm `(mult(v) log |u|_v)_v`
of a unit `u` of `𝓞 K`. This is the exact sequence
`0 → ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ| → Pic^(𝓞 K) → Cl(K) → 0`,
whose left term is the quotient by the image `TauCeti.unitLogSubgroup` of `unitLogEmbedding`.

These are the compactified divisors of Szpiro; they model the hermitian line bundles over
`Spec 𝓞 K` (the divisor `(𝔞, λ)` corresponds to `𝔞⁻¹` with the norms `e^{-λ_v / mult(v)} |·|_v`),
and in Gillet–Soulé's language their classes form `\widehat{CH}¹(Spec 𝓞 K)`.

## Main definitions

* `TauCeti.ArakelovDivisor K`: the Arakelov divisors `(𝔞, λ)` of `K`, an additive group.
* `TauCeti.ArakelovDivisor.degree`: the Arakelov degree `log N(𝔞) + Σ_v λ_v`.
* `TauCeti.ArakelovDivisor.principal`: the principal divisor of an element of `Kˣ`.
* `TauCeti.ArakelovDivisor.ofInfinitePart`: the divisor `(𝓞 K, λ)` supported at infinity.
* `TauCeti.ArakelovDivisor.ofFinitePart`: the divisor `(𝔞, 0)` with no archimedean part.
* `TauCeti.ArakelovPicardGroup K`: Arakelov divisors modulo principal divisors.
* `TauCeti.ArakelovPicardGroup.degree`, `TauCeti.ArakelovPicardGroup.toClassGroup`: the degree
  and the ideal class of a class of Arakelov divisors.
* `TauCeti.ArakelovPicardGroup.ofInfinitePartQuotient`: the map
  `ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ| → Pic^(𝓞 K)`.

## Main results

* `TauCeti.ArakelovDivisor.degree_principal`: principal divisors have degree zero (the product
  formula).
* `TauCeti.ArakelovPicardGroup.ofInfinitePartQuotient_injective`,
  `TauCeti.ArakelovPicardGroup.exact_ofInfinitePartQuotient_toClassGroup` and
  `TauCeti.ArakelovPicardGroup.toClassGroup_surjective`: the exact sequence
  `0 → ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ| → Pic^(𝓞 K) → Cl(K) → 0`.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.1–1.2,
  Proposition 1.1 and Corollaire.
* H. Gillet, C. Soulé, *Arithmetic intersection theory*, Publ. Math. IHÉS 72 (1990), §3.4.3.
* R. Schoof, *Computing Arakelov class groups*, in *Algorithmic Number Theory*, MSRI Publ. 44
  (2008), §§4–6.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti

variable (K : Type*) [Field K]

/-- An **Arakelov divisor** of a number field `K`: a pair `(𝔞, λ)` of an invertible fractional
ideal `𝔞` of `𝓞 K`, the finite part `∏ 𝔭 ^ n_𝔭`, and a real coefficient `λ_v` at each infinite
place `v`. It stands for the formal sum `Σ_𝔭 n_𝔭 [𝔭] + Σ_v λ_v [v]`. The structure and its group
law make sense over any field; the degree and the principal divisors need `K` to be a number
field. -/
@[ext]
structure ArakelovDivisor where
  /-- The finite part `𝔞 = ∏ 𝔭 ^ n_𝔭` of an Arakelov divisor, an invertible fractional ideal. -/
  finitePart : (FractionalIdeal (𝓞 K)⁰ K)ˣ
  /-- The archimedean coefficient `λ_v` of an Arakelov divisor at the infinite place `v`. -/
  infinitePart : InfinitePlace K → ℝ

namespace ArakelovDivisor

variable {K}

instance : Zero (ArakelovDivisor K) := ⟨⟨1, 0⟩⟩

instance : Add (ArakelovDivisor K) :=
  ⟨fun D D' ↦ ⟨D.finitePart * D'.finitePart, D.infinitePart + D'.infinitePart⟩⟩

instance : Neg (ArakelovDivisor K) := ⟨fun D ↦ ⟨D.finitePart⁻¹, -D.infinitePart⟩⟩

instance : Sub (ArakelovDivisor K) :=
  ⟨fun D D' ↦ ⟨D.finitePart / D'.finitePart, D.infinitePart - D'.infinitePart⟩⟩

instance : SMul ℕ (ArakelovDivisor K) := ⟨fun n D ↦ ⟨D.finitePart ^ n, n • D.infinitePart⟩⟩

instance : SMul ℤ (ArakelovDivisor K) := ⟨fun n D ↦ ⟨D.finitePart ^ n, n • D.infinitePart⟩⟩

@[simp] theorem finitePart_zero : (0 : ArakelovDivisor K).finitePart = 1 := (rfl)

@[simp] theorem infinitePart_zero : (0 : ArakelovDivisor K).infinitePart = 0 := (rfl)

@[simp] theorem finitePart_add (D D' : ArakelovDivisor K) :
    (D + D').finitePart = D.finitePart * D'.finitePart := (rfl)

@[simp] theorem infinitePart_add (D D' : ArakelovDivisor K) :
    (D + D').infinitePart = D.infinitePart + D'.infinitePart := (rfl)

@[simp] theorem finitePart_neg (D : ArakelovDivisor K) : (-D).finitePart = D.finitePart⁻¹ :=
  (rfl)

@[simp] theorem infinitePart_neg (D : ArakelovDivisor K) :
    (-D).infinitePart = -D.infinitePart := (rfl)

@[simp] theorem finitePart_sub (D D' : ArakelovDivisor K) :
    (D - D').finitePart = D.finitePart / D'.finitePart := (rfl)

@[simp] theorem infinitePart_sub (D D' : ArakelovDivisor K) :
    (D - D').infinitePart = D.infinitePart - D'.infinitePart := (rfl)

@[simp] theorem finitePart_nsmul (n : ℕ) (D : ArakelovDivisor K) :
    (n • D).finitePart = D.finitePart ^ n := (rfl)

@[simp] theorem infinitePart_nsmul (n : ℕ) (D : ArakelovDivisor K) :
    (n • D).infinitePart = n • D.infinitePart := (rfl)

@[simp] theorem finitePart_zsmul (n : ℤ) (D : ArakelovDivisor K) :
    (n • D).finitePart = D.finitePart ^ n := (rfl)

@[simp] theorem infinitePart_zsmul (n : ℤ) (D : ArakelovDivisor K) :
    (n • D).infinitePart = n • D.infinitePart := (rfl)

/-- Arakelov divisors form an additive group under the componentwise group law: multiplication
of finite parts and addition of archimedean coefficients. -/
instance : AddCommGroup (ArakelovDivisor K) :=
  Function.Injective.addCommGroup
    (fun D : ArakelovDivisor K ↦ (Additive.ofMul D.finitePart, D.infinitePart))
    (fun _ _ h ↦ ArakelovDivisor.ext (congrArg (fun p ↦ p.1.toMul) h) (congrArg Prod.snd h))
    (rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

variable (K)

/-- The Arakelov divisor `(𝓞 K, λ) = Σ_v λ_v [v]` supported at the infinite places. -/
def ofInfinitePart : (InfinitePlace K → ℝ) →+ ArakelovDivisor K where
  toFun l := ⟨1, l⟩
  map_zero' := rfl
  map_add' _ _ := ArakelovDivisor.ext (one_mul 1).symm rfl

variable {K}

@[simp] theorem finitePart_ofInfinitePart (l : InfinitePlace K → ℝ) :
    (ofInfinitePart K l).finitePart = 1 := (rfl)

@[simp] theorem infinitePart_ofInfinitePart (l : InfinitePlace K → ℝ) :
    (ofInfinitePart K l).infinitePart = l := (rfl)

variable (K) in
/-- The Arakelov divisor `(𝔞, 0) = Σ_𝔭 n_𝔭 [𝔭]` with finite part `𝔞` and no archimedean part. -/
def ofFinitePart : Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ →+ ArakelovDivisor K where
  toFun 𝔞 := ⟨𝔞.toMul, 0⟩
  map_zero' := rfl
  map_add' _ _ := ArakelovDivisor.ext rfl (add_zero 0).symm

@[simp] theorem finitePart_ofFinitePart (𝔞 : Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (ofFinitePart K 𝔞).finitePart = 𝔞.toMul := (rfl)

@[simp] theorem infinitePart_ofFinitePart (𝔞 : Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (ofFinitePart K 𝔞).infinitePart = 0 := (rfl)

/-- Every Arakelov divisor is the sum of its finite part and its part at the infinite places. -/
theorem ofFinitePart_add_ofInfinitePart (D : ArakelovDivisor K) :
    ofFinitePart K (Additive.ofMul D.finitePart) + ofInfinitePart K D.infinitePart = D :=
  ArakelovDivisor.ext (mul_one _) (zero_add _)

variable [NumberField K]

variable (K)

/-- The **Arakelov degree** `deg^(𝔞, λ) = log N(𝔞) + Σ_v λ_v` of an Arakelov divisor, where
`N(𝔞)` is the absolute norm of the finite part. -/
def degree : ArakelovDivisor K →+ ℝ :=
  AddMonoidHom.mk'
    (fun D ↦ Real.log (absNorm (D.finitePart : FractionalIdeal (𝓞 K)⁰ K) : ℝ) +
      ∑ v, D.infinitePart v)
    fun D D' ↦ by
      have absNorm_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          ((absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) ≠ 0 :=
        Rat.cast_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr I.ne_zero)
      simp only [finitePart_add, Units.val_mul, map_mul, Rat.cast_mul, infinitePart_add,
        Pi.add_apply, Finset.sum_add_distrib,
        Real.log_mul (absNorm_ne_zero D.finitePart) (absNorm_ne_zero D'.finitePart)]
      ring

variable {K}

/-- The defining formula of the Arakelov degree. -/
theorem degree_apply (D : ArakelovDivisor K) :
    degree K D = Real.log (absNorm (D.finitePart : FractionalIdeal (𝓞 K)⁰ K) : ℝ) +
      ∑ v, D.infinitePart v := (rfl)

@[simp] theorem degree_ofInfinitePart (l : InfinitePlace K → ℝ) :
    degree K (ofInfinitePart K l) = ∑ v, l v := by
  simp [degree_apply]

@[simp] theorem degree_ofFinitePart (𝔞 : Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    degree K (ofFinitePart K 𝔞) =
      Real.log (absNorm (𝔞.toMul : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  simp [degree_apply]

variable (K)

/-- The **principal Arakelov divisor** `(f) = (f 𝓞 K, v ↦ -mult(v) log |f|_v)` of `f ∈ Kˣ`. The
weight `mult(v)` counts the two complex embeddings inducing a complex place `v`. -/
def principal : Additive Kˣ →+ ArakelovDivisor K where
  toFun f := ⟨toPrincipalIdeal (𝓞 K) K f.toMul, fun v ↦ -(v.mult * Real.log (v (f.toMul : K)))⟩
  map_zero' := by
    ext1
    · simp
    · ext v
      simp
  map_add' f g := by
    ext1
    · simp
    · ext v
      simp only [toMul_add, Units.val_mul, map_mul, infinitePart_add, Pi.add_apply,
        Real.log_mul (pos_iff.mpr f.toMul.ne_zero).ne' (pos_iff.mpr g.toMul.ne_zero).ne']
      ring

variable {K}

@[simp] theorem finitePart_principal (f : Additive Kˣ) :
    (principal K f).finitePart = toPrincipalIdeal (𝓞 K) K f.toMul := (rfl)

@[simp] theorem infinitePart_principal (f : Additive Kˣ) (v : InfinitePlace K) :
    (principal K f).infinitePart v = -(v.mult * Real.log (v (f.toMul : K))) := (rfl)

/-- **Principal Arakelov divisors have degree zero.** The finite part of `(f)` has norm
`|N_{K/ℚ}(f)|`, and this is the product formula `∏_v |f|_v ^ mult(v) = |N_{K/ℚ}(f)|`. -/
@[simp] theorem degree_principal (f : Additive Kˣ) : degree K (principal K f) = 0 := by
  have hf : (f.toMul : K) ≠ 0 := f.toMul.ne_zero
  have hprod : Real.log (∏ v : InfinitePlace K, v (f.toMul : K) ^ v.mult) =
      ∑ v : InfinitePlace K, v.mult * Real.log (v (f.toMul : K)) := by
    rw [Real.log_prod fun v _ ↦ pow_ne_zero _ (pos_iff.mpr hf).ne']
    simp [Real.log_pow]
  rw [degree_apply, finitePart_principal, coe_toPrincipalIdeal, absNorm_span_singleton]
  simp only [infinitePart_principal, Finset.sum_neg_distrib, ← hprod, prod_eq_abs_norm,
    Rat.cast_abs]
  ring

/-- The principal divisor of a unit `u` of `𝓞 K` is supported at infinity, with archimedean part
minus the weighted logarithm `(mult(v) log |u|_v)_v` of the unit. -/
theorem principal_unit (u : (𝓞 K)ˣ) :
    principal K (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) u)) =
      -ofInfinitePart K (unitLogEmbedding K (Additive.ofMul u) : InfinitePlace K → ℝ) := by
  ext1
  · simpa using (toPrincipalIdeal_eq_one_iff (K := K) _).mpr ⟨u, rfl⟩
  · ext v
    simp

end ArakelovDivisor

variable [NumberField K] in
/-- The **compactified Picard group** (Arakelov divisor class group) of a number field `K`: the
Arakelov divisors modulo the principal divisors. In Gillet–Soulé's language this is
`\widehat{CH}¹(Spec 𝓞 K)`. -/
abbrev ArakelovPicardGroup : Type _ := ArakelovDivisor K ⧸ (ArakelovDivisor.principal K).range

namespace ArakelovPicardGroup

variable [NumberField K]

open ArakelovDivisor

/-- The class of an Arakelov divisor in the compactified Picard group. -/
def mk : ArakelovDivisor K →+ ArakelovPicardGroup K := QuotientAddGroup.mk' _

variable {K}

/-- The quotient coercion `↑D` into the compactified Picard group, as produced for instance by
`QuotientAddGroup.induction_on`, is the class `mk K D`; as a simp lemma it brings the coercion to
the `mk` form on which the API below is stated. -/
@[simp] theorem coe_eq_mk (D : ArakelovDivisor K) : (D : ArakelovPicardGroup K) = mk K D := (rfl)

/-- Every class in the compactified Picard group is the class of an Arakelov divisor. -/
theorem mk_surjective : Function.Surjective (mk K) := QuotientAddGroup.mk'_surjective _

/-- Two Arakelov divisors have the same class exactly when they differ by a principal divisor. -/
theorem mk_eq_mk_iff {D D' : ArakelovDivisor K} :
    mk K D = mk K D' ↔ ∃ f : Additive Kˣ, D + principal K f = D' := by
  rw [mk, QuotientAddGroup.mk'_eq_mk']
  simp only [AddMonoidHom.mem_range, exists_exists_eq_and]

/-- An Arakelov divisor has trivial class exactly when it is principal. -/
theorem mk_eq_zero_iff {D : ArakelovDivisor K} :
    mk K D = 0 ↔ ∃ f : Additive Kˣ, principal K f = D := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]

@[simp] theorem mk_principal (f : Additive Kˣ) : mk K (principal K f) = 0 :=
  mk_eq_zero_iff.mpr ⟨f, rfl⟩

variable (K)

/-- The Arakelov degree of a class of Arakelov divisors, well defined since principal divisors
have degree zero (`TauCeti.ArakelovDivisor.degree_principal`). -/
def degree : ArakelovPicardGroup K →+ ℝ :=
  QuotientAddGroup.lift _ (ArakelovDivisor.degree K) <| by
    rintro _ ⟨f, rfl⟩
    exact degree_principal f

variable {K}

@[simp] theorem degree_mk (D : ArakelovDivisor K) :
    degree K (mk K D) = ArakelovDivisor.degree K D := (rfl)

variable (K)

/-- The ideal class `[𝔞]` of the finite part of a class of Arakelov divisors `(𝔞, λ)`. -/
def toClassGroup : ArakelovPicardGroup K →+ Additive (ClassGroup (𝓞 K)) :=
  QuotientAddGroup.lift _
    { toFun D := Additive.ofMul (ClassGroup.mk K D.finitePart)
      map_zero' := by simp
      map_add' D D' := by simp [ofMul_mul] } <| by
    rintro _ ⟨f, rfl⟩
    simp

variable {K}

@[simp] theorem toClassGroup_mk (D : ArakelovDivisor K) :
    toClassGroup K (mk K D) = Additive.ofMul (ClassGroup.mk K D.finitePart) := (rfl)

/-- The ideal class of the divisor `(𝔞, 0)` is the class of `𝔞`. -/
theorem toClassGroup_mk_ofFinitePart (𝔞 : Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    toClassGroup K (mk K (ArakelovDivisor.ofFinitePart K 𝔞)) =
      Additive.ofMul (ClassGroup.mk K 𝔞.toMul) := (rfl)

/-- Every ideal class is the class of the finite part of an Arakelov divisor. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup K) := fun c ↦
  ClassGroup.induction K (P := fun c ↦ ∃ P, toClassGroup K P = Additive.ofMul c)
    (fun I ↦ ⟨mk K (ArakelovDivisor.ofFinitePart K (Additive.ofMul I)),
      toClassGroup_mk_ofFinitePart _⟩) c.toMul

variable (K)

/-- The class of the Arakelov divisor `(𝓞 K, λ)` supported at the infinite places. -/
def ofInfinitePart : (InfinitePlace K → ℝ) →+ ArakelovPicardGroup K :=
  (mk K).comp (ArakelovDivisor.ofInfinitePart K)

variable {K}

@[simp] theorem mk_ofInfinitePart (l : InfinitePlace K → ℝ) :
    mk K (ArakelovDivisor.ofInfinitePart K l) = ofInfinitePart K l := (rfl)

@[simp] theorem degree_ofInfinitePart (l : InfinitePlace K → ℝ) :
    degree K (ofInfinitePart K l) = ∑ v, l v := by
  rw [← mk_ofInfinitePart, degree_mk, ArakelovDivisor.degree_ofInfinitePart]

@[simp] theorem toClassGroup_ofInfinitePart (l : InfinitePlace K → ℝ) :
    toClassGroup K (ofInfinitePart K l) = 0 := by
  simp [← mk_ofInfinitePart]

/-- **Exactness in the middle.** A class of Arakelov divisors has trivial ideal class exactly
when it is the class of a divisor supported at the infinite places. -/
theorem exact_ofInfinitePart_toClassGroup :
    Function.Exact (ofInfinitePart K) (toClassGroup K) := by
  intro P
  constructor
  · intro hP
    obtain ⟨D, rfl⟩ := mk_surjective P
    rw [toClassGroup_mk, ofMul_eq_zero, ClassGroup.mk_eq_one_iff_exists] at hP
    obtain ⟨f, hf⟩ := hP
    refine ⟨(D - principal K (Additive.ofMul f)).infinitePart, ?_⟩
    have hD : D - principal K (Additive.ofMul f) =
        ArakelovDivisor.ofInfinitePart K (D - principal K (Additive.ofMul f)).infinitePart := by
      ext1
      · simp [hf]
      · rfl
    rw [← mk_ofInfinitePart, ← hD, map_sub, mk_principal, sub_zero]
  · rintro ⟨l, rfl⟩
    exact toClassGroup_ofInfinitePart l

/-- **The kernel on the archimedean side is the unit lattice.** The class of a divisor
`(𝓞 K, λ)` supported at infinity is trivial exactly when `λ` is the weighted logarithm
`(mult(v) log |u|_v)_v` of a unit `u` of `𝓞 K`. -/
theorem ofInfinitePart_eq_zero_iff {l : InfinitePlace K → ℝ} :
    ofInfinitePart K l = 0 ↔ l ∈ unitLogSubgroup K := by
  rw [← mk_ofInfinitePart, mk_eq_zero_iff, mem_unitLogSubgroup]
  constructor
  · rintro ⟨f, hf⟩
    have hfin := congrArg ArakelovDivisor.finitePart hf
    rw [finitePart_principal, finitePart_ofInfinitePart] at hfin
    obtain ⟨z, hz⟩ := (toPrincipalIdeal_eq_one_iff _).mp hfin
    have hinf := congrArg ArakelovDivisor.infinitePart hf
    rw [← ofMul_toMul f, ← hz, principal_unit] at hinf
    exact ⟨z⁻¹, by simpa using hinf⟩
  · rintro ⟨u, rfl⟩
    refine ⟨-Additive.ofMul (Units.map (algebraMap (𝓞 K) K) u), ?_⟩
    rw [map_neg, principal_unit, neg_neg]

variable (K)

/-- The injection `ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ| → Pic^(𝓞 K)`: the descent of
`TauCeti.ArakelovPicardGroup.ofInfinitePart` to the quotient by the weighted logarithms
`(mult(v) log |u|_v)_v` of the units `u` of `𝓞 K`. -/
def ofInfinitePartQuotient :
    (InfinitePlace K → ℝ) ⧸ unitLogSubgroup K →+ ArakelovPicardGroup K :=
  QuotientAddGroup.lift _ (ofInfinitePart K) fun _ ↦ ofInfinitePart_eq_zero_iff.mpr

variable {K}

@[simp] theorem ofInfinitePartQuotient_mk (l : InfinitePlace K → ℝ) :
    ofInfinitePartQuotient K (QuotientAddGroup.mk l) = ofInfinitePart K l := (rfl)

/-- **Exactness on the left.** The map `ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ| → Pic^(𝓞 K)` is
injective. -/
theorem ofInfinitePartQuotient_injective : Function.Injective (ofInfinitePartQuotient K) := by
  refine (injective_iff_map_eq_zero _).mpr fun q hq ↦ ?_
  induction q using QuotientAddGroup.induction_on with | H l => ?_
  exact (QuotientAddGroup.eq_zero_iff l).mpr (ofInfinitePart_eq_zero_iff.mp hq)

/-- **Exactness in the middle**, for the map out of `ℝ^{InfinitePlace K} / log |(𝓞 K)ˣ|`. -/
theorem exact_ofInfinitePartQuotient_toClassGroup :
    Function.Exact (ofInfinitePartQuotient K) (toClassGroup K) := by
  intro P
  rw [exact_ofInfinitePart_toClassGroup P]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨QuotientAddGroup.mk l, rfl⟩
  · rintro ⟨q, rfl⟩
    induction q using QuotientAddGroup.induction_on with | H l => exact ⟨l, rfl⟩

end ArakelovPicardGroup

end TauCeti
