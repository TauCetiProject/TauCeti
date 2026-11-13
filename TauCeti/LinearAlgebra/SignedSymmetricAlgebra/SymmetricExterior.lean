/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.Algebra.CharP.Invertible
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The signed symmetric algebra of an evenly or oddly graded module

If an internally graded module `V` is concentrated in even degrees, the Koszul sign
`(-1) ^ (p * q)` is always `1`, so the signed symmetric algebra `A(V) = TauCeti.SignedSym G` is
the ordinary symmetric algebra of `V`, carrying `lengthPiece G n` onto homogeneous polynomials of
degree `n`. If `V` is concentrated in odd degrees, the sign is always `-1`: over any commutative
ring `A(V)` maps surjectively onto `ExteriorAlgebra R V` (`TauCeti.SignedSym.toExteriorAlgebra`),
carrying `lengthPiece G n` onto `⋀[R]^n V`, and once `2` is invertible in the coefficients `A(V)`
is isomorphic to the exterior algebra of `V` (`TauCeti.SignedSym.exteriorAlgebraEquiv`), yielding
module finiteness for finite `V`, rank `2 ^ finrank R V` for finite free `V` over a nontrivial
ring, and vanishing of `lengthPiece G d` above `finrank R V`. For the general mixed-parity
comparison `A(V) ≃ Sym(V_even) ⊗ Λ(V_odd)`, see
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.ParityDecomposition`.

When `V` is concentrated in degree `1`, `toExteriorAlgebra` maps `signedSymPiece G p` onto
`TauCeti.ExteriorAlgebra.integerGrading R V p` over any commutative ring, `exteriorAlgebraEquiv`
identifies them isomorphically when `2` is invertible, and `signedSymPiece G p` vanishes above
`finrank R V` for finite free `V`.

The invertibility of `2` cannot be dropped in the odd equivalence: over `ℤ`, the relation only
gives `2 • x ^ 2 = 0` for an odd generator `x`, while `x ^ 2 = 0` holds in the exterior algebra.
Conversely, Mathlib's `SymmetricAlgebra` is the wrong carrier for odd generators, since there
`x ^ 2 ≠ 0`.

The inverse of the symmetric comparison is built from `SymmetricAlgebra.lift`, which only maps
into commutative algebras. It is applied with values in the center of `A(V)`, which contains the
generators when `V` is concentrated in even degrees.

## Main definitions and results

* `TauCeti.SignedSym.commute_generator_of_piece_odd_eq_bot` and
  `TauCeti.SignedSym.mul_comm_of_piece_odd_eq_bot`: for an evenly graded `V`, generators commute,
  hence `A(V)` is commutative.
* `TauCeti.SignedSym.symmetricAlgebraEquiv` and
  `TauCeti.SignedSym.map_lengthPiece_symmetricAlgebraEquiv`: for an evenly graded `V`,
  `A(V) ≃ Sym(V)` compatibly with word length, over any commutative ring.
* `TauCeti.SignedSym.generator_mul_generator_eq_neg_of_piece_even_eq_bot` and
  `TauCeti.SignedSym.generator_mul_self_eq_zero_of_piece_even_eq_bot`: for an oddly graded `V`,
  generators anticommute, and square to zero when `2` is invertible.
* `TauCeti.SignedSym.toExteriorAlgebra`, `TauCeti.SignedSym.toExteriorAlgebra_surjective`, and
  `TauCeti.SignedSym.map_lengthPiece_toExteriorAlgebra`: characteristic-free surjection
  `A(V) →ₐ[R] Λ(V)` and exterior-power compatibility for oddly graded `V`.
* `TauCeti.SignedSym.exteriorAlgebraEquiv`: for an oddly graded `V` and invertible `2`,
  `A(V) ≃ Λ(V)`, giving `lengthPiece_eq_bot_of_piece_even_eq_bot_of_finrank_lt`,
  `finite_of_piece_even_eq_bot`, and `finrank_eq_two_pow_of_piece_even_eq_bot`.
* `TauCeti.SignedSym.map_signedSymPiece_toExteriorAlgebra_of_piece_eq_bot` and
  `TauCeti.SignedSym.signedSymPiece_eq_bot_of_piece_eq_bot_of_finrank_lt`: degree-`1` input-degree
  compatibility with `TauCeti.ExteriorAlgebra.integerGrading R V` and top-degree vanishing.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {G : InternalGrading R V ℤ}

/-- A commutation rule with a fixed sign `s` between generators of homogeneous elements holds
between all generators. -/
private theorem generator_mul_generator_eq_smul (s : ℤ)
    (h : ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      generator G x * generator G y = s • (generator G y * generator G x)) (x y : V) :
    generator G x * generator G y = s • (generator G y * generator G x) := by
  have key : (LinearMap.mul R (SignedSym G)).compl₁₂ (generator G) (generator G) =
      s • (LinearMap.mul R (SignedSym G)).flip.compl₁₂ (generator G) (generator G) :=
    G.linearMap_ext fun p x hx => G.linearMap_ext fun q y hy => by
      simpa using h p q x y hx hy
  simpa using LinearMap.congr_fun₂ key x y

/-! ### Even generators -/

section Even

variable (hG : ∀ p, Odd p → G.piece p = ⊥)
include hG

/-- If `V` is concentrated in even degrees, the Koszul sign of a nonzero homogeneous element
against any degree is `1`. -/
private theorem eq_zero_or_negOnePow_eq_one_of_piece_odd_eq_bot {p : ℤ} {x : V}
    (hx : x ∈ G.piece p) (q : ℤ) : x = 0 ∨ (p * q).negOnePow = 1 := by
  rcases Int.even_or_odd p with hp | hp
  · exact .inr (Int.negOnePow_even _ (hp.mul_right q))
  · exact .inl (by simpa [hG p hp] using hx)

/-- If `V` is concentrated in even degrees, any two generators of `A(V)` commute. -/
theorem commute_generator_of_piece_odd_eq_bot (x y : V) :
    Commute (generator G x) (generator G y) := by
  refine (commute_iff_eq _ _).2 ?_
  simpa using generator_mul_generator_eq_smul 1 (fun p q x y hx hy => by
    rcases eq_zero_or_negOnePow_eq_one_of_piece_odd_eq_bot hG hx q with rfl | h
    · simp
    · simpa [h] using generator_mul_generator G hx hy) x y

/-- If `V` is concentrated in even degrees, the generators of `A(V)` are central. -/
private theorem generator_mem_center (x : V) :
    generator G x ∈ Subalgebra.center R (SignedSym G) := by
  refine Subalgebra.mem_center_iff.2 fun b => ?_
  induction b using SignedSym.induction with
  | algebraMap r => exact Algebra.commutes r _
  | generator y => exact commute_generator_of_piece_odd_eq_bot hG y x
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/-- If `V` is concentrated in even degrees, `A(V)` is commutative. -/
theorem mul_comm_of_piece_odd_eq_bot (a b : SignedSym G) : a * b = b * a := by
  have hcenter : ∀ a : SignedSym G, a ∈ Subalgebra.center R (SignedSym G) := by
    intro a
    induction a using SignedSym.induction with
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | generator x => exact generator_mem_center hG x
    | mul a b ha hb => exact mul_mem ha hb
    | add a b ha hb => exact add_mem ha hb
  exact ((Subalgebra.mem_center_iff.1 (hcenter a)) b).symm

/-- The map `A(V) → Sym(V)` fixing generators, for `V` concentrated in even degrees. -/
private def toSymmetricAlgebra : SignedSym G →ₐ[R] SymmetricAlgebra R V :=
  lift G (SymmetricAlgebra.ι R V) fun p q x y hx _ => by
    rcases eq_zero_or_negOnePow_eq_one_of_piece_odd_eq_bot hG hx q with rfl | h
    · simp
    · simp [h, mul_comm]

/-- The map `Sym(V) → A(V)` fixing generators, for `V` concentrated in even degrees. It takes
values in the center of `A(V)`, which is commutative. -/
private noncomputable def ofSymmetricAlgebra : SymmetricAlgebra R V →ₐ[R] SignedSym G :=
  (Subalgebra.center R (SignedSym G)).val.comp <| SymmetricAlgebra.lift <|
    (generator G).codRestrict (Subalgebra.center R (SignedSym G)).toSubmodule
      (generator_mem_center hG)

private theorem ofSymmetricAlgebra_ι (x : V) :
    ofSymmetricAlgebra hG (SymmetricAlgebra.ι R V x) = generator G x := by
  rw [ofSymmetricAlgebra, AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, Subalgebra.coe_val]
  -- The subalgebra and its underlying submodule have the same subtype coercion.
  exact LinearMap.codRestrict_apply _ (generator G) (h := generator_mem_center hG) x

/-- **The signed symmetric algebra of an evenly graded module is its symmetric algebra.** If `V`
is concentrated in even degrees, `A(V)` is isomorphic to `SymmetricAlgebra R V`, compatibly with
the generators. -/
noncomputable def symmetricAlgebraEquiv : SignedSym G ≃ₐ[R] SymmetricAlgebra R V :=
  AlgEquiv.ofAlgHom (toSymmetricAlgebra hG) (ofSymmetricAlgebra hG)
    (SymmetricAlgebra.algHom_ext <| LinearMap.ext fun x => by
      simp [toSymmetricAlgebra, ofSymmetricAlgebra_ι])
    (hom_ext G fun x => by simp [toSymmetricAlgebra, ofSymmetricAlgebra_ι])

/-- The symmetric comparison sends the generator of `x` to `x`. -/
@[simp]
theorem symmetricAlgebraEquiv_generator (x : V) :
    symmetricAlgebraEquiv hG (generator G x) = SymmetricAlgebra.ι R V x := by
  simp [symmetricAlgebraEquiv, toSymmetricAlgebra]

/-- The inverse symmetric comparison sends `x` to its generator. -/
@[simp]
theorem symmetricAlgebraEquiv_symm_ι (x : V) :
    (symmetricAlgebraEquiv hG).symm (SymmetricAlgebra.ι R V x) = generator G x := by
  rw [AlgEquiv.symm_apply_eq, symmetricAlgebraEquiv_generator]

/-- `symmetricAlgebraEquiv` identifies word-length pieces with the homogeneous polynomial
submodules of `SymmetricAlgebra R V`. -/
theorem map_lengthPiece_symmetricAlgebraEquiv (n : ℕ) :
    (lengthPiece G n).map (symmetricAlgebraEquiv hG).toLinearMap =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n := by
  rw [lengthPiece_def, TauCeti.SymmetricAlgebra.homogeneousSubmodule]
  refine (Submodule.map_pow _ (symmetricAlgebraEquiv hG).toAlgHom n).trans ?_
  rw [← LinearMap.range_comp]
  congr 2
  ext x
  simp

/-- Membership in the degree-`n` homogeneous submodule of `SymmetricAlgebra R V` corresponds to
word length `n` in `SignedSym G`. -/
@[simp]
theorem symmetricAlgebraEquiv_mem_homogeneousSubmodule_iff {n : ℕ} {a : SignedSym G} :
    symmetricAlgebraEquiv hG a ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n ↔
      a ∈ lengthPiece G n := by
  simp [← map_lengthPiece_symmetricAlgebraEquiv hG n]

/-- The inverse of `symmetricAlgebraEquiv` lands in `lengthPiece G n` precisely on the degree-`n`
homogeneous submodule of `SymmetricAlgebra R V`. -/
@[simp]
theorem symmetricAlgebraEquiv_symm_mem_lengthPiece_iff {n : ℕ} {s : SymmetricAlgebra R V} :
    (symmetricAlgebraEquiv hG).symm s ∈ lengthPiece G n ↔
      s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n := by
  rw [← symmetricAlgebraEquiv_mem_homogeneousSubmodule_iff hG, AlgEquiv.apply_symm_apply]

end Even

/-! ### Odd generators -/

section Odd

variable (hG : ∀ p, Even p → G.piece p = ⊥)
include hG

/-- If `V` is concentrated in odd degrees, the Koszul sign of two nonzero homogeneous elements is
`-1`. -/
private theorem eq_zero_or_eq_zero_or_negOnePow_eq_neg_one_of_piece_even_eq_bot {p q : ℤ}
    {x y : V} (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    x = 0 ∨ y = 0 ∨ (p * q).negOnePow = -1 := by
  rcases Int.even_or_odd p with hp | hp
  · exact .inl (by simpa [hG p hp] using hx)
  rcases Int.even_or_odd q with hq | hq
  · exact .inr (.inl (by simpa [hG q hq] using hy))
  exact .inr (.inr (Int.negOnePow_odd _ (hp.mul hq)))

/-- If `V` is concentrated in odd degrees, any two generators of `A(V)` anticommute. -/
theorem generator_mul_generator_eq_neg_of_piece_even_eq_bot (x y : V) :
    generator G x * generator G y = -(generator G y * generator G x) := by
  simpa using generator_mul_generator_eq_smul (-1) (fun p q x y hx hy => by
    rcases eq_zero_or_eq_zero_or_negOnePow_eq_neg_one_of_piece_even_eq_bot hG hx hy with
      rfl | rfl | h
    · simp
    · simp
    · simpa [h] using generator_mul_generator G hx hy) x y

/-- If `V` is concentrated in odd degrees and `2` is invertible, every generator of `A(V)` squares
to zero. -/
theorem generator_mul_self_eq_zero_of_piece_even_eq_bot [Invertible (2 : R)] (x : V) :
    generator G x * generator G x = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R)
    (generator_mul_generator_eq_neg_of_piece_even_eq_bot hG x x)

/-- When all even-degree pieces of `V` vanish, `SignedSym G` maps canonically to
`ExteriorAlgebra R V` over any commutative ring, with no invertibility of `2` required. -/
def toExteriorAlgebra : SignedSym G →ₐ[R] ExteriorAlgebra R V :=
  lift G (ExteriorAlgebra.ι R) fun p q x y hx hy => by
    rcases eq_zero_or_eq_zero_or_negOnePow_eq_neg_one_of_piece_even_eq_bot hG hx hy with
      rfl | rfl | h
    · simp
    · simp
    · simpa [h] using eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) x y)

/-- `toExteriorAlgebra` sends each generator of `SignedSym G` to the canonical exterior
generator. -/
@[simp]
theorem toExteriorAlgebra_generator (x : V) :
    toExteriorAlgebra hG (generator G x) = ExteriorAlgebra.ι R x := by
  simp [toExteriorAlgebra]

/-- Over any commutative ring, `toExteriorAlgebra hG` is surjective onto `ExteriorAlgebra R V`. -/
theorem toExteriorAlgebra_surjective : Function.Surjective (toExteriorAlgebra hG) :=
  ExteriorAlgebra.induction
    (fun r => ⟨algebraMap R _ r, AlgHom.commutes _ r⟩)
    (fun x => ⟨generator G x, toExteriorAlgebra_generator hG x⟩)
    (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩)

/-- Over any commutative ring, `toExteriorAlgebra` maps `lengthPiece G n` onto the `n`-th exterior
power. -/
theorem map_lengthPiece_toExteriorAlgebra (n : ℕ) :
    (lengthPiece G n).map (toExteriorAlgebra hG).toLinearMap = ⋀[R]^n V := by
  rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    ← LinearMap.range_comp]
  congr 2
  ext x
  simp

/-- Over any commutative ring, `toExteriorAlgebra` maps words of length `n` into the `n`-th
exterior power. -/
theorem toExteriorAlgebra_mem_exteriorPower {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) :
    toExteriorAlgebra hG a ∈ ⋀[R]^n V := by
  rw [← map_lengthPiece_toExteriorAlgebra hG n, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

section InvertibleTwo

variable [Invertible (2 : R)]

/-- The map `Λ(V) → A(V)` fixing generators, for `V` concentrated in odd degrees and invertible
`2`. -/
private noncomputable def ofExteriorAlgebra : ExteriorAlgebra R V →ₐ[R] SignedSym G :=
  ExteriorAlgebra.lift R ⟨generator G, generator_mul_self_eq_zero_of_piece_even_eq_bot hG⟩

/-- **The signed symmetric algebra of an oddly graded module is its exterior algebra.** If `V` is
concentrated in odd degrees and `2` is invertible in `R`, then `A(V)` is isomorphic to
`ExteriorAlgebra R V`, compatibly with the generators. -/
noncomputable def exteriorAlgebraEquiv : SignedSym G ≃ₐ[R] ExteriorAlgebra R V :=
  AlgEquiv.ofAlgHom (toExteriorAlgebra hG) (ofExteriorAlgebra hG)
    (ExteriorAlgebra.hom_ext <| LinearMap.ext fun x => by
      simp [ofExteriorAlgebra])
    (hom_ext G fun x => by simp [ofExteriorAlgebra])

/-- The exterior comparison sends the generator of `x` to `x`. -/
@[simp]
theorem exteriorAlgebraEquiv_generator (x : V) :
    exteriorAlgebraEquiv hG (generator G x) = ExteriorAlgebra.ι R x := by
  simp [exteriorAlgebraEquiv]

/-- The inverse exterior comparison sends `x` to its generator. -/
@[simp]
theorem exteriorAlgebraEquiv_symm_ι (x : V) :
    (exteriorAlgebraEquiv hG).symm (ExteriorAlgebra.ι R x) = generator G x := by
  rw [AlgEquiv.symm_apply_eq, exteriorAlgebraEquiv_generator]

/-- The forward direction of `exteriorAlgebraEquiv` is `toExteriorAlgebra`. Not `@[simp]` so
`exteriorAlgebraEquiv hG` remains in `AlgEquiv` normal form alongside
`exteriorAlgebraEquiv_generator`. -/
theorem exteriorAlgebraEquiv_apply (a : SignedSym G) :
    exteriorAlgebraEquiv hG a = toExteriorAlgebra hG a := by
  simp [exteriorAlgebraEquiv]

/-- The underlying algebra homomorphism of `exteriorAlgebraEquiv` is `toExteriorAlgebra`. -/
@[simp]
theorem exteriorAlgebraEquiv_toAlgHom :
    (exteriorAlgebraEquiv hG).toAlgHom = toExteriorAlgebra hG :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- The underlying linear map of `exteriorAlgebraEquiv` is that of `toExteriorAlgebra`. -/
@[simp]
theorem exteriorAlgebraEquiv_toLinearMap :
    (exteriorAlgebraEquiv hG).toLinearMap = (toExteriorAlgebra hG).toLinearMap :=
  AlgEquiv.toLinearMap_ofAlgHom _ _ _ _

/-- Applying `(exteriorAlgebraEquiv hG).symm` after `toExteriorAlgebra hG` recovers the original
element. -/
@[simp]
theorem exteriorAlgebraEquiv_symm_toExteriorAlgebra (a : SignedSym G) :
    (exteriorAlgebraEquiv hG).symm (toExteriorAlgebra hG a) = a := by
  rw [← exteriorAlgebraEquiv_apply hG a, AlgEquiv.symm_apply_apply]

/-- Applying `toExteriorAlgebra hG` after `(exteriorAlgebraEquiv hG).symm` recovers the original
exterior element. -/
@[simp]
theorem toExteriorAlgebra_exteriorAlgebraEquiv_symm (e : ExteriorAlgebra R V) :
    toExteriorAlgebra hG ((exteriorAlgebraEquiv hG).symm e) = e := by
  rw [← exteriorAlgebraEquiv_apply hG, AlgEquiv.apply_symm_apply]

end InvertibleTwo

/-- When `2` is invertible, membership of `toExteriorAlgebra hG a` in the `n`-th exterior power
corresponds to word length `n` in `SignedSym G`. -/
@[simp]
theorem toExteriorAlgebra_mem_exteriorPower_iff [Invertible (2 : R)] {n : ℕ} {a : SignedSym G} :
    toExteriorAlgebra hG a ∈ ⋀[R]^n V ↔ a ∈ lengthPiece G n := by
  refine ⟨fun h => ?_, toExteriorAlgebra_mem_exteriorPower hG⟩
  rw [← map_lengthPiece_toExteriorAlgebra hG n] at h
  obtain ⟨b, hb, hab⟩ := h
  rwa [← exteriorAlgebraEquiv_symm_toExteriorAlgebra hG a, ← hab,
    AlgHom.toLinearMap_apply, exteriorAlgebraEquiv_symm_toExteriorAlgebra]

/-- Membership of `exteriorAlgebraEquiv hG a` in the `n`-th exterior power corresponds to word
length `n` in `SignedSym G`. -/
@[simp]
theorem exteriorAlgebraEquiv_mem_exteriorPower_iff [Invertible (2 : R)] {n : ℕ}
    {a : SignedSym G} :
    exteriorAlgebraEquiv hG a ∈ ⋀[R]^n V ↔ a ∈ lengthPiece G n := by
  rw [exteriorAlgebraEquiv_apply, toExteriorAlgebra_mem_exteriorPower_iff]

/-- When `2` is invertible, the inverse of `exteriorAlgebraEquiv` lands in `lengthPiece G n`
precisely on the `n`-th exterior power. -/
@[simp]
theorem exteriorAlgebraEquiv_symm_mem_lengthPiece_iff [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R V} :
    (exteriorAlgebraEquiv hG).symm e ∈ lengthPiece G n ↔ e ∈ ⋀[R]^n V := by
  rw [← toExteriorAlgebra_mem_exteriorPower_iff hG, toExteriorAlgebra_exteriorAlgebraEquiv_symm]

/-- When `2` is invertible and all even-degree pieces of a finite free `R`-module `V` vanish,
every word-length piece of `SignedSym G` above `finrank R V` vanishes. -/
theorem lengthPiece_eq_bot_of_piece_even_eq_bot_of_finrank_lt [Invertible (2 : R)]
    [Module.Free R V] [Module.Finite R V] {d : ℕ} (hd : Module.finrank R V < d) :
    lengthPiece G d = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hmem : exteriorAlgebraEquiv hG a ∈ ⋀[R]^d V :=
    (exteriorAlgebraEquiv_mem_exteriorPower_iff hG).mpr ha
  have hzero : exteriorAlgebraEquiv hG a = 0 :=
    congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt d hd ⟨_, hmem⟩)
  exact (exteriorAlgebraEquiv hG).injective (hzero.trans (map_zero _).symm)

/-- When `2` is invertible and all even-degree pieces of a finite `R`-module `V` vanish,
`SignedSym G` is a finite `R`-module. -/
theorem finite_of_piece_even_eq_bot [Invertible (2 : R)] [Module.Finite R V] :
    Module.Finite R (SignedSym G) :=
  Module.Finite.equiv (exteriorAlgebraEquiv hG).symm.toLinearEquiv

/-- When `2` is invertible and all even-degree pieces of a finite free `R`-module `V` vanish,
`SignedSym G` has rank `2 ^ finrank R V`. -/
theorem finrank_eq_two_pow_of_piece_even_eq_bot [Nontrivial R] [Invertible (2 : R)]
    [Module.Free R V] [Module.Finite R V] :
    Module.finrank R (SignedSym G) = 2 ^ Module.finrank R V := by
  rw [(exteriorAlgebraEquiv hG).toLinearEquiv.finrank_eq,
    TauCeti.ExteriorAlgebra.finrank_eq_two_pow]

end Odd

/-! ### Degree-one generators -/

section DegreeOne

/-- When `V` is concentrated in degree `1`, `toExteriorAlgebra` maps the input-degree piece
`signedSymPiece G p` onto `TauCeti.ExteriorAlgebra.integerGrading R V p` for every integer `p`,
over any commutative ring. -/
theorem map_signedSymPiece_toExteriorAlgebra_of_piece_eq_bot (hG : ∀ q, q ≠ 1 → G.piece q = ⊥)
    (p : ℤ) (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    (signedSymPiece G p).map (toExteriorAlgebra hG').toLinearMap =
      TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [signedSymPiece_eq_bot_of_piece_eq_bot_of_forall_mul_ne G hG (fun n => by omega),
      Submodule.map_bot, TauCeti.ExteriorAlgebra.integerGrading_of_neg hp]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have hn : signedSymPiece G (n : ℤ) = lengthPiece G n := by
      simpa only [mul_one] using signedSymPiece_eq_lengthPiece_of_piece_eq_bot G one_ne_zero hG n
    rw [hn, TauCeti.ExteriorAlgebra.integerGrading_natCast, map_lengthPiece_toExteriorAlgebra]

/-- When `V` is concentrated in degree `1`, `toExteriorAlgebra` maps elements of input degree `p`
into `TauCeti.ExteriorAlgebra.integerGrading R V p`, over any commutative ring. -/
theorem toExteriorAlgebra_mem_integerGrading_of_piece_eq_bot (hG : ∀ q, q ≠ 1 → G.piece q = ⊥)
    {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    toExteriorAlgebra hG' a ∈ TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rw [← map_signedSymPiece_toExteriorAlgebra_of_piece_eq_bot hG p hG', ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- When `V` is concentrated in degree `1` and `2` is invertible, membership of
`toExteriorAlgebra` in `TauCeti.ExteriorAlgebra.integerGrading R V p` characterizes
`signedSymPiece G p`. -/
theorem toExteriorAlgebra_mem_integerGrading_iff_of_piece_eq_bot [Invertible (2 : R)]
    (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ} {a : SignedSym G}
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    toExteriorAlgebra hG' a ∈ TauCeti.ExteriorAlgebra.integerGrading R V p ↔
      a ∈ signedSymPiece G p := by
  refine ⟨fun h => ?_, fun h => toExteriorAlgebra_mem_integerGrading_of_piece_eq_bot hG h hG'⟩
  rw [← map_signedSymPiece_toExteriorAlgebra_of_piece_eq_bot hG p hG'] at h
  obtain ⟨b, hb, hab⟩ := h
  rwa [← exteriorAlgebraEquiv_symm_toExteriorAlgebra hG' a, ← hab,
    AlgHom.toLinearMap_apply, exteriorAlgebraEquiv_symm_toExteriorAlgebra]

/-- When `V` is concentrated in degree `1` and `2` is invertible, membership of
`exteriorAlgebraEquiv` in `TauCeti.ExteriorAlgebra.integerGrading R V p` characterizes
`signedSymPiece G p`. -/
theorem exteriorAlgebraEquiv_mem_integerGrading_iff_of_piece_eq_bot [Invertible (2 : R)]
    (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ} {a : SignedSym G}
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    exteriorAlgebraEquiv hG' a ∈ TauCeti.ExteriorAlgebra.integerGrading R V p ↔
      a ∈ signedSymPiece G p := by
  rw [exteriorAlgebraEquiv_apply, toExteriorAlgebra_mem_integerGrading_iff_of_piece_eq_bot hG]

/-- When `V` is concentrated in degree `1` and `2` is invertible, the inverse of
`exteriorAlgebraEquiv` lands in `signedSymPiece G p` precisely on
`TauCeti.ExteriorAlgebra.integerGrading R V p`. -/
theorem exteriorAlgebraEquiv_symm_mem_signedSymPiece_iff_of_piece_eq_bot [Invertible (2 : R)]
    (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ} {e : ExteriorAlgebra R V}
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    (exteriorAlgebraEquiv hG').symm e ∈ signedSymPiece G p ↔
      e ∈ TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rw [← toExteriorAlgebra_mem_integerGrading_iff_of_piece_eq_bot hG,
    toExteriorAlgebra_exteriorAlgebraEquiv_symm]

/-- When `V` is a finite free `R`-module concentrated in degree `1` and `2` is invertible, every
input-degree piece of `SignedSym G` above `finrank R V` vanishes. -/
theorem signedSymPiece_eq_bot_of_piece_eq_bot_of_finrank_lt [Invertible (2 : R)] [Module.Free R V]
    [Module.Finite R V] (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ}
    (hp : (Module.finrank R V : ℤ) < p) :
    signedSymPiece G p = ⊥ := by
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt ((Nat.cast_nonneg _).trans_lt hp))
  have hd : signedSymPiece G (d : ℤ) = lengthPiece G d := by
    simpa only [mul_one] using signedSymPiece_eq_lengthPiece_of_piece_eq_bot G one_ne_zero hG d
  rw [hd]
  exact lengthPiece_eq_bot_of_piece_even_eq_bot_of_finrank_lt
    (fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) (Nat.cast_lt.mp hp)

end DegreeOne

end TauCeti.SignedSym
