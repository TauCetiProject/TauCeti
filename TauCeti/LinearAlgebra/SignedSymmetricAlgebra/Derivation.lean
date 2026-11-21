/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.DirectSum.HomogeneousExtend
import TauCeti.LinearAlgebra.Matrix.Triangular.Derivation

/-!
# Odd derivations of the signed symmetric algebra

For an internally graded module `V` over any Koszul-signed degree semiring `ι` (such as `ℤ` or
`ZMod 2`), a linear map `δ : V → A(V)` into the signed symmetric algebra
`A(V) = TauCeti.SignedSym G` which shifts degree by any Koszul-odd degree `k : ι`
(`(-1 : ℤˣ) ^ k = -1`, covering cohomological degree `1 : ℤ`, homological degree `-1 : ℤ`, and
odd parity `1 : ZMod 2`) extends uniquely to a linear endomorphism `d` of `A(V)` satisfying the
signed Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b)` for `a` of degree `p`.

This extension `TauCeti.SignedSym.liftDerivation` again shifts degree by `k`. Its square is an
unsigned derivation, so it vanishes as soon as it vanishes on generators. When `ι = ℤ` and
`k = 1`, `d` is the differential of a differential graded algebra structure on `A(V)` exactly when
`d (δ x) = 0` for every `x : V`. This reduces the identity `d ∘ d = 0` for the differential of a
free supercommutative algebra, such as the contact homology differential in either integer or
parity grading, to a check on generators.

The extension is constructed through the universal property of `A(V)` using the shared
lower-triangular `2 × 2` matrix construction in `TauCeti.LinearAlgebra.Matrix.Triangular.Derivation`
(`TauCeti.triangularDerivationMap`, `TauCeti.triangularDerivation`): the matrices
`[[a, 0], [d a, σ a]]`, where `σ` is the grade involution `a ↦ (-1) ^ |a| • a`, multiply as
`a + ε d a` in the dual numbers over `A(V)` with one odd generator `ε`. The signed Leibniz rule
for `d` is multiplicativity of `a ↦ [[a, 0], [d a, σ a]]`.

## Main definitions

* `TauCeti.SignedSym.liftDerivation`: the odd derivation extending a degree-`k` assignment on
  generators for any Koszul-odd degree `k : ι` (`(-1 : ℤˣ) ^ k = -1`).

## Main results

* `TauCeti.SignedSym.apply_map_eq_map_apply_of_leibniz`: a graded algebra map out of `A(V)`
  intertwines signed Leibniz maps whenever it does so on generators.
* `TauCeti.SignedSym.liftDerivation_mul`: the signed Leibniz rule.
* `TauCeti.SignedSym.isHomogeneous_liftDerivation`: the extension has degree `k`.
* `TauCeti.SignedSym.eq_liftDerivation` and `TauCeti.SignedSym.existsUnique_odd_extension`:
  an odd derivation is determined by its values on generators.
* `TauCeti.SignedSym.comp_self_eq_zero_iff`: a Koszul-odd-degree signed Leibniz map squares to
  zero if and only if its square vanishes on generators.
* `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff`: for integer gradings and degree `1`, the
  extension is a differential graded algebra differential if and only if it kills the image of the
  assignment.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra on which the contact homology differential is defined.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

section General

variable {ι : Type*} [DecidableEq ι] [CommSemiring ι] [Module ι (Additive ℤˣ)]
variable {G : InternalGrading R V ι}

/-- A linear map out of `A(V)` satisfying a Leibniz rule along an algebra map `f`, with an
arbitrary sign `s p` for a left factor of degree `p`, and vanishing on generators, is zero.
This covers differences of intertwined odd derivations and squares of odd derivations. -/
private theorem eq_zero_of_leibniz {A : Type*} [Ring A] [Algebra R A]
    (s : ι → ℤˣ) (f : SignedSym G →ₐ[R] A) {D : SignedSym G →ₗ[R] A}
    (hD : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      D (a * b) = D a * f b + s p • (f a * D b))
    (hgen : ∀ x, D (generator G x) = 0) : D = 0 := by
  have hone : D 1 = 0 := by
    have h := hD (SetLike.GradedOne.one_mem (A := signedSymPiece G)) 1
    simp only [map_one, mul_one, one_mul, left_eq_add] at h
    exact (smul_eq_zero_iff_eq (s 0)).1 h
  have hhom : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → D a = 0 := by
    intro p a ha
    refine (homogeneous_induction G (P := fun p a => a ∈ signedSymPiece G p ∧ D a = 0)
      ⟨SetLike.GradedOne.one_mem, hone⟩
      (fun p x hx => ⟨generator_mem_signedSymPiece G hx, hgen x⟩)
      (fun p q a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
        rw [hD ha.1, ha.2, hb.2, zero_mul, mul_zero, smul_zero, zero_add]⟩)
      (fun p => ⟨zero_mem _, map_zero D⟩)
      (fun p a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩)
      (fun p r a ha => ⟨Submodule.smul_mem _ r ha.1, by rw [map_smul, ha.2, smul_zero]⟩)
      ha).2
  ext a
  induction a using DirectSum.Decomposition.inductionOn (signedSymPiece G) with
  | zero => simp
  | homogeneous a => exact hhom a.property
  | add a b ha hb => simp_all

/-- A graded algebra map out of `A(V)` intertwines signed Leibniz maps if it does so on
all generators. Neither degree-shift nor square-zero hypotheses are needed. -/
theorem apply_map_eq_map_apply_of_leibniz {A : Type*} [Ring A] [Algebra R A]
    {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
    {dV : SignedSym G →ₗ[R] SignedSym G}
    (hV : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p →
      ∀ b, dV (a * b) = dV a * b + ((-1 : ℤˣ) ^ p) • (a * dV b))
    {d : A →ₗ[R] A}
    (hd : ∀ {p : ι} {a : A}, a ∈ 𝒜 p →
      ∀ b, d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b))
    (f : signedSymPiece G →ₐᵍ[R] 𝒜)
    (hgen : ∀ x, d (f (generator G x)) = f (dV (generator G x)))
    (a : SignedSym G) : d (f a) = f (dV a) := by
  have hzero : d ∘ₗ f.toAlgHom.toLinearMap - f.toAlgHom.toLinearMap ∘ₗ dV = 0 := by
    refine eq_zero_of_leibniz (fun p ↦ (-1 : ℤˣ) ^ p) f.toAlgHom (fun {p a} ha b => ?_)
      (fun x => by simp [hgen x])
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      GradedAlgHom.coe_toAlgHom, map_mul,
      hd (Graded.map_mem f ha), hV ha, map_add, map_zsmul, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  exact sub_eq_zero.mp (LinearMap.congr_fun hzero a)

section Lift

variable (δ : V →ₗ[R] SignedSym G)

/-- The twisted generator assignment `x ↦ (-1) ^ p • generator G x` for `x` of degree `p`. -/
private noncomputable def twistGenerator (G : InternalGrading R V ι) : V →ₗ[R] SignedSym G :=
  DirectSum.homogeneousExtend G.piece
    (fun p ↦ ((((-1 : ℤˣ) ^ p).val : R) • generator G) ∘ₗ (G.piece p).subtype)

private theorem twistGenerator_of_mem {p : ι} {x : V} (hx : x ∈ G.piece p) :
    twistGenerator G x = ((-1 : ℤˣ) ^ p) • generator G x := by
  rw [twistGenerator, DirectSum.homogeneousExtend_of_mem G.piece _ hx]
  simp [Int.cast_smul_eq_zsmul, Units.smul_def]

/-- The grade involution `a ↦ (-1) ^ |a| • a` of `A(V)`. -/
private noncomputable def twist (G : InternalGrading R V ι) : SignedSym G →ₐ[R] SignedSym G :=
  lift G (twistGenerator G) fun p q x y hx hy ↦ by
    rw [twistGenerator_of_mem hx, twistGenerator_of_mem hy, smul_mul_assoc, mul_smul_comm,
      generator_mul_generator G hx hy, mul_smul_comm, smul_mul_assoc]
    simp only [smul_smul]
    congr 1
    ac_rfl

private theorem twist_of_mem {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) :
    twist G a = ((-1 : ℤˣ) ^ p) • a := by
  refine homogeneous_induction G (P := fun p a ↦ twist G a = ((-1 : ℤˣ) ^ p) • a)
    (by simp)
    (fun p x hx ↦ by simp [twist, twistGenerator_of_mem hx])
    (fun p q a b ha hb ↦ by
      rw [map_mul, ha, hb, smul_mul_assoc, mul_smul_comm, smul_smul, ← uzpow_add])
    (fun _ ↦ by simp [Units.smul_def])
    (fun _ a b ha hb ↦ by simp only [map_add, ha, hb, Units.smul_def, zsmul_add])
    (fun _ r a ha ↦ by rw [map_smul, ha, smul_comm])
    ha

variable {δ} {k : ι}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) k)
variable (hk : (-1 : ℤˣ) ^ k = -1)

variable (δ) in
/-- The odd derivation of `A(V)` extending a linear map `δ : V → A(V)` of Koszul-odd degree `k`
(`(-1 : ℤˣ) ^ k = -1`). It satisfies the signed Leibniz rule
`TauCeti.SignedSym.liftDerivation_mul`, has degree `k`, and is the unique such extension of `δ`
(`TauCeti.SignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : SignedSym G →ₗ[R] SignedSym G :=
  triangularDerivation <|
    lift G (triangularDerivationMap (generator G) (twist G) δ) fun p q x y hx hy ↦ by
      have hgx := generator_mem_signedSymPiece G hx
      have hgy := generator_mem_signedSymPiece G hy
      refine triangularDerivationMap_mul_eq_smul_mul (generator G) (twist G) δ
        (s₁ := (-1 : ℤˣ) ^ p) (s₂ := (-1 : ℤˣ) ^ q) (generator_mul_generator G hx hy) ?_ ?_
        (twist_of_mem hgx) (twist_of_mem hgy)
      · rw [show (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ q = (-1 : ℤˣ) ^ ((p + k) * q) by
          rw [add_mul, uzpow_add, uzpow_mul (-1) k q, hk]]
        exact mul_eq_uzpow_smul_mul G (hδ.map_mem hx) hgy
      · rw [show (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ p = (-1 : ℤˣ) ^ (p * (q + k)) by
          rw [mul_add, uzpow_add, mul_comm p k, uzpow_mul (-1) k p, hk]]
        exact mul_eq_uzpow_smul_mul G hgx (hδ.map_mem hy)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ hk (generator G x) = δ x := by
  simp [liftDerivation]

/-- **The signed Leibniz rule**: for a left factor of degree `p`,
`d (a * b) = d a * b + (-1) ^ p • (a * d b)`. -/
theorem liftDerivation_mul {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (b : SignedSym G) :
    liftDerivation δ hδ hk (a * b) =
      liftDerivation δ hδ hk a * b + ((-1 : ℤˣ) ^ p) • (a * liftDerivation δ hδ hk b) := by
  have htop : Algebra.adjoin R (Set.range (generator G)) = ⊤ :=
    top_unique fun x _ ↦ SignedSym.induction G (algebraMap_mem _)
      (fun m ↦ Algebra.subset_adjoin ⟨m, rfl⟩) (fun _ _ ↦ mul_mem) (fun _ _ ↦ add_mem) x
  rw [liftDerivation, triangularDerivation_mul (twist G) htop (by rintro _ ⟨x, rfl⟩; simp),
    twist_of_mem ha, smul_mul_assoc]

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ hk 1 = 0 :=
  map_one_eq_zero_of_leibniz (signedSymPiece G) (liftDerivation_mul hδ hk)

/-- The odd derivation annihilates the coefficients. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) : liftDerivation δ hδ hk (algebraMap R _ r) = 0 :=
  map_algebraMap_of_leibniz (signedSymPiece G) (liftDerivation_mul hδ hk) r

/-- The odd derivation shifts degree by `k`. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ hk) (signedSymPiece G) (signedSymPiece G) k := by
  refine LinearMap.isHomogeneous_def.2 fun p a ha => ?_
  refine (homogeneous_induction G
    (P := fun p a => a ∈ signedSymPiece G p ∧ liftDerivation δ hδ hk a ∈ signedSymPiece G (p + k))
    ⟨SetLike.GradedOne.one_mem, by simp⟩
    (fun p x hx => ⟨generator_mem_signedSymPiece G hx, by simpa using hδ.map_mem hx⟩)
    (fun p q a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
      rw [liftDerivation_mul hδ hk ha.1]
      refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
      · simpa [add_right_comm] using SetLike.mul_mem_graded ha.2 hb.1
      · simpa [add_assoc] using SetLike.mul_mem_graded ha.1 hb.2⟩)
    (fun p => ⟨zero_mem _, by simp⟩)
    (fun p a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩)
    (fun p r a ha => ⟨Submodule.smul_mem _ r ha.1, by
      rw [map_smul]; exact Submodule.smul_mem _ r ha.2⟩)
    ha).2

/-- **Uniqueness of odd derivations**: a linear endomorphism of `A(V)` satisfying the signed
Leibniz rule and agreeing with `δ` on generators is `liftDerivation δ hδ hk`. No degree condition
on the endomorphism is needed. -/
theorem eq_liftDerivation {d : SignedSym G →ₗ[R] SignedSym G}
    (hleibniz : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ hk := by
  ext a
  exact apply_map_eq_map_apply_of_leibniz (liftDerivation_mul hδ hk) hleibniz
    (.id R _) (fun x => by simp [hgen x]) a

end Lift

/-- **Odd derivations are free on generators**: a linear map `δ : V → A(V)` of Koszul-odd degree
`k` (`(-1 : ℤˣ) ^ k = -1`) extends uniquely to a linear endomorphism of `A(V)` satisfying the
signed Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] SignedSym G} {k : ι}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) k) (hk : (-1 : ℤˣ) ^ k = -1) :
    ∃! d : SignedSym G →ₗ[R] SignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
        d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b) :=
  ⟨liftDerivation δ hδ hk,
    ⟨LinearMap.ext (liftDerivation_generator hδ hk), liftDerivation_mul hδ hk⟩,
    fun _ hd => eq_liftDerivation hδ hk hd.2 fun x => LinearMap.congr_fun hd.1 x⟩

/-- **The square of an odd derivation is determined by generators**: a linear endomorphism of
`A(V)` of Koszul-odd degree `k` (`(-1 : ℤˣ) ^ k = -1`) satisfying the signed Leibniz rule squares
to zero if and only if its square vanishes on generators. The square is an unsigned derivation,
since the two cross terms of the signed Leibniz rule cancel. -/
theorem comp_self_eq_zero_iff {d : SignedSym G →ₗ[R] SignedSym G} {k : ι}
    (hdeg : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) k)
    (hk : (-1 : ℤˣ) ^ k = -1)
    (hleibniz : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 := by
  refine ⟨fun h x => LinearMap.congr_fun h (generator G x), fun h => ?_⟩
  refine eq_zero_of_leibniz 1 (AlgHom.id R _) (fun {p a} ha b => ?_) h
  simp only [AlgHom.id_apply]
  have hda := hdeg.map_mem ha
  have hpk : (-1 : ℤˣ) ^ (p + k) = -((-1 : ℤˣ) ^ p) := by
    rw [uzpow_add, hk, mul_neg, mul_one]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hleibniz ha, map_add,
    map_zsmul_unit, hleibniz hda, hleibniz ha, hpk]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul, zsmul_add, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_zsmul, Pi.one_apply]
  abel

end General

section Int

variable {G : InternalGrading R V ℤ}

/-- **The extension is a differential**: for integer gradings,
`liftDerivation δ hδ (uzpow_one (-1))` makes `A(V)` a differential graded algebra if and only if
it annihilates `δ x` for every `x : V`. -/
theorem isDGAlgebra_liftDerivation_iff {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ (uzpow_one (-1))) ↔
      ∀ x, liftDerivation δ hδ (uzpow_one (-1)) (δ x) = 0 := by
  refine ⟨fun h x => by simpa using h.sq_zero (generator G x), fun h => ?_⟩
  have hsq := (comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ (uzpow_one (-1)))
    (uzpow_one (-1)) (liftDerivation_mul hδ (uzpow_one (-1)))).2 (by simpa using h)
  exact
    { map_mem := fun ha => (isHomogeneous_liftDerivation hδ (uzpow_one (-1))).map_mem ha
      sq_zero := fun a => LinearMap.congr_fun hsq a
      leibniz := fun ha b => liftDerivation_mul hδ (uzpow_one (-1)) ha b }

end Int

end TauCeti.SignedSym
