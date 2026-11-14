/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition

/-!
# Nikulin generator decompositions of finite quadratic modules

Nikulin's Proposition 1.8.1 decomposes every nondegenerate finite quadratic module as an orthogonal
sum of four families of primary generators:

* `q_θ^{(p)}(p^k)` on `ℤ/p^k`, for an odd prime `p`, `k ≥ 1`, and `p ∤ θ`;
* `q_θ^{(2)}(2^k)` on `ℤ/2^k`, for `k ≥ 1` and `θ` odd;
* `u^{(2)}(2^k)` and `v^{(2)}(2^k)` on `(ℤ/2^k)²`, for `k ≥ 1`.

This file packages generator labels into an inductive type `NikulinGenerator`, forms the orthogonal
sum `orthogonalSumNikulinGenerators` of any finite list of generators, and bundles a generator
decomposition of `A` as `NikulinDecomposition A`.

## Main definitions and results

* `TauCeti.FiniteQuadraticModule.NikulinGenerator`: label for one of Nikulin's primary generators,
  together with `IsAdmissible`, `prime`, `exponent`, `rank`, `unitCoeff`,
  `toFiniteQuadraticModule`, and `realizationDet`.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.isAdmissible_iff`: a generator is admissible
  if and only if its finite quadratic module is nondegenerate and nontrivial.
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`: orthogonal sum of a list of
  generators, with append, cardinality, nondegeneracy, and rank formulas.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition`: a list of admissible generators together
  with an isometry from `A` onto their orthogonal sum; every nondegenerate module admits one
  (`IsNondegenerate.exists_nikulinDecomposition`).
* `TauCeti.FiniteQuadraticModule.primaryComponent` and
  `TauCeti.FiniteQuadraticModule.NikulinDecomposition.primaryComponent`: filtering a decomposition
  by a prime `p` produces a decomposition of the `p`-primary component, whose additive group rank
  equals the sum of the realization ranks of its `p`-primary generators
  (`NikulinDecomposition.rank_primaryComponent`).
* `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`: existence of an orthogonal summand
  `q_θ^{(2)}(2)` (`θ` odd), the dyadic exception in Nikulin's Theorems 1.9.1 and 1.10.1.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979), §1.8–1.10.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

/-! ## Generator labels and their invariants -/

/-- **Nikulin's primary generators** (Nikulin, Proposition 1.8.1): the odd cyclic module
`q_θ^{(p)}(p^k)` for an odd prime `p`, the dyadic cyclic module `q_θ^{(2)}(2^k)` for `k ≥ 1`, and
the two dyadic rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)`. -/
inductive NikulinGenerator where
  | oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ)
  | dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ)
  | dyadicU (k : ℕ)
  | dyadicV (k : ℕ)

/-- Positive exponent and unit parameter: the generators whose finite quadratic modules are
nondegenerate and nontrivial. -/
@[expose, simp] def NikulinGenerator.IsAdmissible : NikulinGenerator → Prop
  | .oddCyclic p k _ _ θ => 0 < k ∧ ¬ (p : ℤ) ∣ θ
  | .dyadicCyclic _ _ θ => Odd θ
  | .dyadicU k => 0 < k
  | .dyadicV k => 0 < k

/-- The prime at which a generator is primary. -/
@[expose, simp] def NikulinGenerator.prime : NikulinGenerator → ℕ
  | .oddCyclic p _ _ _ _ => p
  | .dyadicCyclic _ _ _ => 2
  | .dyadicU _ => 2
  | .dyadicV _ => 2

/-- The prime-power exponent `k` of a generator `q_θ^{(p)}(p^k)`, `u^{(2)}(2^k)`, or
`v^{(2)}(2^k)`. -/
@[expose, simp] def NikulinGenerator.exponent : NikulinGenerator → ℕ
  | .oddCyclic _ k _ _ _ => k
  | .dyadicCyclic k _ _ => k
  | .dyadicU k => k
  | .dyadicV k => k

/-- The rank of the minimal `p`-adic lattice realization of a generator (`1` for cyclic generators,
`2` for `u^{(2)}(2^k)` and `v^{(2)}(2^k)`). -/
@[expose, simp] def NikulinGenerator.rank : NikulinGenerator → ℕ
  | .oddCyclic _ _ _ _ _ => 1
  | .dyadicCyclic _ _ _ => 1
  | .dyadicU _ => 2
  | .dyadicV _ => 2

/-- The unit factor in the Gram determinant of the minimal `p`-adic realization of a generator:
`θ` for cyclic generators, `-1` for `u^{(2)}(2^k)`, and `3` for `v^{(2)}(2^k)`. -/
@[expose, simp] def NikulinGenerator.unitCoeff : NikulinGenerator → ℤ
  | .oddCyclic _ _ _ _ θ => θ
  | .dyadicCyclic _ _ θ => θ
  | .dyadicU _ => -1
  | .dyadicV _ => 3

/-- The finite quadratic module represented by a generator label. -/
@[expose] noncomputable def NikulinGenerator.toFiniteQuadraticModule :
    NikulinGenerator → FiniteQuadraticModule.{0}
  | .oddCyclic p k _ hodd θ => FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ
  | .dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      FiniteQuadraticModule.dyadicCyclic k θ
  | .dyadicU k => FiniteQuadraticModule.dyadicU k
  | .dyadicV k => FiniteQuadraticModule.dyadicV k

/-- **The Gram determinant of the minimal `p`-adic realization of a generator**: `θ · p^k` for
`q_θ^{(p)}(p^k)`, `θ · 2^k` for `q_θ^{(2)}(2^k)`, `-4^k` for `u^{(2)}(2^k)`, and `3 · 4^k` for
`v^{(2)}(2^k)`. -/
@[expose, simp] def NikulinGenerator.realizationDet : NikulinGenerator → ℤ
  | .oddCyclic p k _ _ θ => θ * (p : ℤ) ^ k
  | .dyadicCyclic k _ θ => θ * 2 ^ k
  | .dyadicU k => -(4 ^ k)
  | .dyadicV k => 3 * 4 ^ k

namespace NikulinGenerator

/-- The prime attached to any generator is prime. -/
theorem prime_prime (g : NikulinGenerator) : g.prime.Prime := by
  cases g with
  | oddCyclic _ _ hp _ _ => exact hp
  | dyadicCyclic _ _ _ | dyadicU _ | dyadicV _ => exact Nat.prime_two

/-- Every generator's realization determinant factors as `unitCoeff` times the module order. -/
theorem realizationDet_eq_unitCoeff_mul_natCard (g : NikulinGenerator) :
    g.realizationDet = g.unitCoeff * (Nat.card g.toFiniteQuadraticModule : ℤ) := by
  cases g with
  | oddCyclic p k _ hodd θ =>
      simp [realizationDet, unitCoeff, toFiniteQuadraticModule]
  | dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      simp [realizationDet, unitCoeff, toFiniteQuadraticModule]
  | dyadicU k =>
      have h4 : (4 : ℤ) ^ k = (2 : ℤ) ^ k * (2 : ℤ) ^ k := by
        rw [← mul_pow]
        norm_num
      simp only [realizationDet, unitCoeff, toFiniteQuadraticModule, natCard_dyadicU, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, h4]
      ring
  | dyadicV k =>
      have h4 : (4 : ℤ) ^ k = (2 : ℤ) ^ k * (2 : ℤ) ^ k := by
        rw [← mul_pow]
        norm_num
      simp only [realizationDet, unitCoeff, toFiniteQuadraticModule, natCard_dyadicV, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, h4]

/-- The order of a generator's finite quadratic module is a power of `g.prime`. -/
theorem exists_pow_natCard (g : NikulinGenerator) :
    ∃ n : ℕ, Nat.card g.toFiniteQuadraticModule = g.prime ^ n := by
  cases g with
  | oddCyclic p k _ _ _ =>
      exact ⟨k, by simp [toFiniteQuadraticModule, prime]⟩
  | dyadicCyclic k hk _ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      exact ⟨k, by simp [toFiniteQuadraticModule, prime]⟩
  | dyadicU k =>
      exact ⟨k + k, by rw [toFiniteQuadraticModule, natCard_dyadicU, prime, pow_add]⟩
  | dyadicV k =>
      exact ⟨k + k, by rw [toFiniteQuadraticModule, natCard_dyadicV, prime, pow_add]⟩

/-- Every element of `g.toFiniteQuadraticModule` lies in its `g.prime`-primary component. -/
theorem mem_primaryComponent_prime (g : NikulinGenerator) (x : g.toFiniteQuadraticModule) :
    x ∈ AddCommGroup.primaryComponent g.toFiniteQuadraticModule g.prime := by
  obtain ⟨n, hn⟩ := g.exists_pow_natCard
  exact AddCommGroup.mem_primaryComponent.mpr ⟨n, hn ▸ card_nsmul_eq_zero' (x := x)⟩

/-- An admissible generator has positive exponent. -/
theorem IsAdmissible.exponent_pos {g : NikulinGenerator} (hg : g.IsAdmissible) :
    0 < g.exponent := by
  cases g with
  | oddCyclic _ _ _ _ _ => exact hg.1
  | dyadicCyclic _ hk _ => exact hk
  | dyadicU _ | dyadicV _ => exact hg

/-- The prime of an admissible generator does not divide its unit determinant factor. -/
theorem IsAdmissible.not_dvd_unitCoeff {g : NikulinGenerator} (hg : g.IsAdmissible) :
    ¬ (g.prime : ℤ) ∣ g.unitCoeff := by
  cases g with
  | oddCyclic _ _ _ _ _ => exact hg.2
  | dyadicCyclic _ _ θ =>
      obtain ⟨t, rfl⟩ := hg
      intro hdvd
      obtain ⟨s, hs⟩ := hdvd
      -- Unfold `prime` and `unitCoeff` on `dyadicCyclic` to expose integer parity.
      change 2 * t + 1 = 2 * s at hs
      omega
  | dyadicU _ => simpa only [prime, unitCoeff] using (by decide : ¬ ((2 : ℕ) : ℤ) ∣ -1)
  | dyadicV _ => simpa only [prime, unitCoeff] using (by decide : ¬ ((2 : ℕ) : ℤ) ∣ 3)

/-- The prime of an admissible generator is coprime to its unit determinant factor. -/
theorem IsAdmissible.isCoprime_prime_unitCoeff {g : NikulinGenerator} (hg : g.IsAdmissible) :
    IsCoprime (g.prime : ℤ) g.unitCoeff :=
  ((Nat.prime_iff_prime_int.mp g.prime_prime).coprime_iff_not_dvd).mpr hg.not_dvd_unitCoeff

/-- An admissible generator produces a nondegenerate finite quadratic module. -/
theorem IsAdmissible.isNondegenerate {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.toFiniteQuadraticModule.IsNondegenerate := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      have hcop : IsCoprime (p : ℤ) θ := hg.isCoprime_prime_unitCoeff
      simpa only [toFiniteQuadraticModule, isNondegenerate_oddCyclic_iff, Nat.cast_pow] using
        hcop.pow_left
  | dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      exact (isNondegenerate_dyadicCyclic_iff k θ).mpr hg
  | dyadicU k => exact isNondegenerate_dyadicU k
  | dyadicV k => exact isNondegenerate_dyadicV k

/-- **Characterization of admissible generators**: `g` is admissible if and only if its finite
quadratic module is nondegenerate and nontrivial (`1 < Nat.card`). -/
theorem isAdmissible_iff (g : NikulinGenerator) :
    g.IsAdmissible ↔
      g.toFiniteQuadraticModule.IsNondegenerate ∧ 1 < Nat.card g.toFiniteQuadraticModule := by
  refine ⟨fun hg ↦ ⟨hg.isNondegenerate, ?_⟩, fun ⟨hnd, hcard⟩ ↦ ?_⟩
  · cases g with
    | oddCyclic p k hp _ _ =>
        simpa only [toFiniteQuadraticModule, natCard_oddCyclic] using
          Nat.one_lt_pow hg.1.ne' hp.one_lt
    | dyadicCyclic k hk _ =>
        let _ : NeZero k := ⟨hk.ne'⟩
        simpa only [toFiniteQuadraticModule, natCard_dyadicCyclic] using
          Nat.one_lt_pow hk.ne' Nat.one_lt_two
    | dyadicU k =>
        dsimp only [IsAdmissible] at hg
        rw [toFiniteQuadraticModule, natCard_dyadicU, ← pow_add]
        exact Nat.one_lt_pow (by omega) Nat.one_lt_two
    | dyadicV k =>
        dsimp only [IsAdmissible] at hg
        rw [toFiniteQuadraticModule, natCard_dyadicV, ← pow_add]
        exact Nat.one_lt_pow (by omega) Nat.one_lt_two
  · cases g with
    | oddCyclic p k hp hodd θ =>
        simp only [toFiniteQuadraticModule, isNondegenerate_oddCyclic_iff, natCard_oddCyclic]
          at hnd hcard
        have hk : 0 < k := Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at hcard
        have hcop : IsCoprime (p : ℤ) θ := by
          rw [Nat.cast_pow] at hnd
          exact IsCoprime.of_isCoprime_of_dvd_left hnd (dvd_pow_self (p : ℤ) hk.ne')
        exact ⟨hk, ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mp hcop⟩
    | dyadicCyclic k hk θ =>
        let _ : NeZero k := ⟨hk.ne'⟩
        exact (isNondegenerate_dyadicCyclic_iff k θ).mp hnd
    | dyadicU k =>
        rw [toFiniteQuadraticModule, natCard_dyadicU] at hcard
        exact Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at hcard
    | dyadicV k =>
        rw [toFiniteQuadraticModule, natCard_dyadicV] at hcard
        exact Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at hcard

/-- An admissible generator has nonzero realization determinant. -/
theorem IsAdmissible.realizationDet_ne_zero {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.realizationDet ≠ 0 := by
  rw [realizationDet_eq_unitCoeff_mul_natCard]
  refine mul_ne_zero (fun h0 ↦ hg.not_dvd_unitCoeff (h0 ▸ dvd_zero _)) ?_
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- For an admissible generator, the additive group rank of `g.toFiniteQuadraticModule` equals its
realization rank (`1` for cyclic generators, `2` for `u^{(2)}` and `v^{(2)}`). -/
theorem IsAdmissible.rank_toFiniteQuadraticModule {g : NikulinGenerator} (hg : g.IsAdmissible) :
    AddGroup.rank g.toFiniteQuadraticModule = g.rank := by
  cases g with
  | oddCyclic p k hp _ _ =>
      exact AddGroup.rank_zmod_of_ne_one (Nat.one_lt_pow hg.1.ne' hp.one_lt).ne'
  | dyadicCyclic k hk _ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      exact AddGroup.rank_zmod_of_ne_one (Nat.one_lt_pow hk.ne' Nat.one_lt_two).ne'
  | dyadicU k | dyadicV k =>
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hg

end NikulinGenerator

/-! ## Orthogonal sums of generator lists -/

/-- The orthogonal sum of a finite list of Nikulin generators; the empty list gives the trivial
module on `PUnit`. -/
@[expose] noncomputable def orthogonalSumNikulinGenerators :
    List NikulinGenerator → FiniteQuadraticModule.{0}
  | [] => ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ)))
  | g :: gs => g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs)

instance : Unique (orthogonalSumNikulinGenerators []) :=
  inferInstanceAs (Unique PUnit.{1})

@[simp]
theorem orthogonalSumNikulinGenerators_nil :
    orthogonalSumNikulinGenerators [] =
      ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ))) :=
  (rfl)

@[simp]
theorem orthogonalSumNikulinGenerators_cons (g : NikulinGenerator) (gs : List NikulinGenerator) :
    orthogonalSumNikulinGenerators (g :: gs) =
      g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs) :=
  (rfl)

/-- Dropping a trivial left factor in an orthogonal product. -/
private def subsingletonProdIsometry (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) [Subsingleton A] : Isometry (A.prod B) B where
  toLinearEquiv :=
    { toFun := Prod.snd
      invFun := fun b ↦ (0, b)
      left_inv := fun ⟨a, _⟩ ↦ Prod.ext (Subsingleton.elim 0 a) rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_app' := fun ⟨a, b⟩ ↦ by
    -- The first coordinate vanishes in a subsingleton module.
    change B.quadratic b = A.quadratic a + B.quadratic b
    rw [Subsingleton.elim a 0, QuadraticMap.map_zero, zero_add]

/-- Appending two generator lists corresponds to taking the orthogonal product of their orthogonal
sums. -/
noncomputable def isometryOrthogonalSumAppend :
    ∀ l₁ l₂ : List NikulinGenerator,
      Isometry (orthogonalSumNikulinGenerators (l₁ ++ l₂))
        ((orthogonalSumNikulinGenerators l₁).prod (orthogonalSumNikulinGenerators l₂))
  | [], _ => (subsingletonProdIsometry (orthogonalSumNikulinGenerators []) _).symm
  | g :: l₁, l₂ =>
      ((QuadraticMap.IsometryEquiv.refl g.toFiniteQuadraticModule.quadratic).prod
        (isometryOrthogonalSumAppend l₁ l₂)).trans
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm

/-- The cardinality of an orthogonal sum of generators is the product of the generator orders. -/
@[simp]
theorem natCard_orthogonalSumNikulinGenerators (gs : List NikulinGenerator) :
    Nat.card (orthogonalSumNikulinGenerators gs) =
      (gs.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod := by
  induction gs with
  | nil => exact Nat.card_unique
  | cons g gs ih =>
      simp only [orthogonalSumNikulinGenerators_cons, List.map_cons, List.prod_cons, ← ih]
      exact Nat.card_prod g.toFiniteQuadraticModule (orthogonalSumNikulinGenerators gs)

/-- An orthogonal sum of generators is nondegenerate if and only if every generator in the list is
nondegenerate. -/
@[simp]
theorem isNondegenerate_orthogonalSumNikulinGenerators_iff (gs : List NikulinGenerator) :
    (orthogonalSumNikulinGenerators gs).IsNondegenerate ↔
      ∀ g ∈ gs, g.toFiniteQuadraticModule.IsNondegenerate := by
  induction gs with
  | nil =>
      exact Iff.intro (fun _ _ hg ↦ False.elim (List.not_mem_nil hg)) fun _ ↦
        (FiniteBilinearModule.isNondegenerate_iff_injective
          (orthogonalSumNikulinGenerators []).toFiniteBilinearModule).mpr
            (Function.injective_of_subsingleton _)
  | cons g gs ih =>
      rw [orthogonalSumNikulinGenerators_cons, isNondegenerate_prod, ih, List.forall_mem_cons]

/-- Any generator appearing in `gs` splits off from `orthogonalSumNikulinGenerators gs` as a left
orthogonal factor. -/
theorem exists_orthogonalSum_of_mem {g : NikulinGenerator} {gs : List NikulinGenerator}
    (h : g ∈ gs) :
    ∃ gs' : List NikulinGenerator,
      Nonempty (Isometry (orthogonalSumNikulinGenerators gs)
        (g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs'))) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h
  refine ⟨l₁ ++ l₂, ⟨?_⟩⟩
  exact (isometryOrthogonalSumAppend l₁ (g :: l₂)).trans
    ((QuadraticMap.IsometryEquiv.prodLeftComm _ _ _).trans
      ((QuadraticMap.IsometryEquiv.refl _).prod (isometryOrthogonalSumAppend l₁ l₂).symm))

private theorem zmodPowToFinOneSurj {p k : ℕ} (hk : 0 < k) :
    ∃ f : ZMod (p ^ k) →+ (Fin 1 → ZMod p), Function.Surjective f := by
  let q : ZMod (p ^ k) →+ ZMod p :=
    (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)).toAddMonoidHom
  have hq : Function.Surjective q := ZMod.castHom_surjective (dvd_pow_self p hk.ne')
  refine ⟨AddMonoidHom.pi fun _ : Fin 1 ↦ q, fun y ↦ ⟨Function.surjInv hq (y 0), ?_⟩⟩
  ext i
  rw [Subsingleton.elim i 0]
  exact Function.surjInv_eq hq (y 0)

/-- Surjection from an admissible `p`-primary generator onto `(Fin g.rank → ZMod p)`, used to pin
down the lower bound on `AddGroup.rank`. -/
private theorem generatorModPrimeSurj {g : NikulinGenerator} {p : ℕ} (hg : g.IsAdmissible)
    (hp : g.prime = p) :
    ∃ f : g.toFiniteQuadraticModule →+ (Fin g.rank → ZMod p), Function.Surjective f := by
  subst hp
  cases g with
  | oddCyclic p k _ _ _ => exact zmodPowToFinOneSurj hg.1
  | dyadicCyclic k hk _ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      exact zmodPowToFinOneSurj hk
  | dyadicU k | dyadicV k =>
      dsimp only [NikulinGenerator.rank, NikulinGenerator.toFiniteQuadraticModule,
        NikulinGenerator.prime] at hg ⊢
      let q : ZMod (2 ^ k) →+ ZMod 2 :=
        (ZMod.castHom (dvd_pow_self 2 hg.ne') (ZMod 2)).toAddMonoidHom
      have hq : Function.Surjective q := ZMod.castHom_surjective (dvd_pow_self 2 hg.ne')
      let f : ZMod (2 ^ k) × ZMod (2 ^ k) →+ (Fin 2 → ZMod 2) :=
        AddMonoidHom.pi (Fin.cases (q.comp (AddMonoidHom.fst _ _))
          fun _ ↦ q.comp (AddMonoidHom.snd _ _))
      refine ⟨f, fun y ↦ ⟨(Function.surjInv hq (y 0), Function.surjInv hq (y 1)), ?_⟩⟩
      ext i
      fin_cases i
      · exact Function.surjInv_eq hq (y 0)
      · exact Function.surjInv_eq hq (y 1)

private def finAppendAddMonoidHom (m n p : ℕ) :
    (Fin m → ZMod p) × (Fin n → ZMod p) →+ (Fin (m + n) → ZMod p) where
  toFun uv := Fin.append uv.1 uv.2
  map_zero' := by
    ext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  map_add' a b := by
    ext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simp [Fin.append_left]
    · simp [Fin.append_right]

private theorem surjective_finAppendAddMonoidHom (m n p : ℕ) :
    Function.Surjective (finAppendAddMonoidHom m n p) := fun w ↦
  ⟨(fun i ↦ w (Fin.castAdd n i), fun j ↦ w (Fin.natAdd m j)), by
    ext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · exact Fin.append_left _ _ i
    · exact Fin.append_right _ _ j⟩

private theorem exists_modPrime_surj_orthogonalSum :
    ∀ {gs : List NikulinGenerator} {p : ℕ},
      (∀ g ∈ gs, g.IsAdmissible) → (∀ g ∈ gs, g.prime = p) →
      ∃ f : orthogonalSumNikulinGenerators gs →+
          (Fin (gs.map NikulinGenerator.rank).sum → ZMod p),
        Function.Surjective f
  | [], _, _, _ =>
      ⟨0, fun _ ↦ ⟨PUnit.unit, funext fun i ↦ Fin.elim0 i⟩⟩
  | g :: gs, p, hadm, hprime => by
      obtain ⟨f₁, hf₁⟩ := generatorModPrimeSurj (hadm g List.mem_cons_self)
        (hprime g List.mem_cons_self)
      obtain ⟨f₂, hf₂⟩ := exists_modPrime_surj_orthogonalSum
        (fun x hx ↦ hadm x (List.mem_cons_of_mem g hx))
        (fun x hx ↦ hprime x (List.mem_cons_of_mem g hx))
      exact ⟨(finAppendAddMonoidHom g.rank _ p).comp (f₁.prodMap f₂),
        (surjective_finAppendAddMonoidHom g.rank _ p).comp (hf₁.prodMap hf₂)⟩

/-- **Rank of a `p`-primary generator sum.** When every generator in `gs` is admissible and
`p`-primary, the additive group rank of `orthogonalSumNikulinGenerators gs` equals the sum of the
generator realization ranks. -/
theorem rank_orthogonalSumNikulinGenerators_eq_sum_of_prime {gs : List NikulinGenerator} {p : ℕ}
    (hp : p.Prime) (hadm : ∀ g ∈ gs, g.IsAdmissible) (hprime : ∀ g ∈ gs, g.prime = p) :
    AddGroup.rank (orthogonalSumNikulinGenerators gs) = (gs.map NikulinGenerator.rank).sum := by
  apply le_antisymm
  · induction gs with
    | nil => exact (AddGroup.rank_eq_zero (orthogonalSumNikulinGenerators [])).le
    | cons g gs ih =>
        have hg := (hadm g List.mem_cons_self).rank_toFiniteQuadraticModule
        have hgs := ih (fun x hx ↦ hadm x (List.mem_cons_of_mem g hx))
          (fun x hx ↦ hprime x (List.mem_cons_of_mem g hx))
        calc AddGroup.rank (orthogonalSumNikulinGenerators (g :: gs))
            ≤ AddGroup.rank g.toFiniteQuadraticModule +
                AddGroup.rank (orthogonalSumNikulinGenerators gs) :=
              AddGroup.rank_prod_le _ _
          _ ≤ g.rank + (gs.map NikulinGenerator.rank).sum := by
              rw [hg]
              exact Nat.add_le_add_left hgs _
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨f, hf⟩ := exists_modPrime_surj_orthogonalSum hadm hprime
    calc (gs.map NikulinGenerator.rank).sum
        = Module.finrank (ZMod p) (Fin (gs.map NikulinGenerator.rank).sum → ZMod p) := by
          rw [Module.finrank_pi (ZMod p), Fintype.card_fin]
      _ = AddGroup.rank (Fin (gs.map NikulinGenerator.rank).sum → ZMod p) :=
          (AddGroup.rank_eq_finrank_zmod _).symm
      _ ≤ AddGroup.rank (orthogonalSumNikulinGenerators gs) :=
          AddGroup.rank_le_of_surjective f hf

/-! ## Bundled Nikulin decompositions -/

/-- A generator decomposition of a finite quadratic module: a list of admissible Nikulin generators
together with an isometry from `A` onto their orthogonal sum. -/
structure NikulinDecomposition (A : FiniteQuadraticModule.{u}) where
  /-- The generator labels in the decomposition. -/
  generators : List NikulinGenerator
  /-- Every generator in the list is admissible (nondegenerate and nontrivial). -/
  admissible : ∀ g ∈ generators, g.IsAdmissible
  /-- Isometry from `A` onto the orthogonal sum of `generators`. -/
  isometry : A.Isometry (orthogonalSumNikulinGenerators generators)

/-- Convert a `Fin n`-indexed orthogonal product of generators into an orthogonal sum over
`List.ofFn`. -/
private noncomputable def piToOrthogonalSumIsometry :
    ∀ {n : ℕ} (g : Fin n → NikulinGenerator),
      Isometry (pi fun i ↦ (g i).toFiniteQuadraticModule)
        (orthogonalSumNikulinGenerators (List.ofFn g))
  | 0, g => by
      rw [List.ofFn_zero]
      exact Isometry.ofSubsingleton
  | n + 1, g => by
      rw [List.ofFn_succ, orthogonalSumNikulinGenerators_cons]
      exact (QuadraticMap.IsometryEquiv.consPi
        fun i ↦ ((g i).toFiniteQuadraticModule).quadratic).symm.trans
          ((QuadraticMap.IsometryEquiv.refl (g 0).toFiniteQuadraticModule.quadratic).prod
            (piToOrthogonalSumIsometry fun i ↦ g i.succ))

private theorem oddCyclic_congr {m₁ m₂ : ℕ} (h : m₁ = m₂) (hm₁ : Odd m₁) (hm₂ : Odd m₂) (θ : ℤ) :
    oddCyclic m₁ hm₁ θ = oddCyclic m₂ hm₂ θ := by
  subst h
  rfl

/-- **Every nondegenerate finite quadratic module admits a Nikulin decomposition.** -/
theorem IsNondegenerate.exists_nikulinDecomposition {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) : Nonempty (NikulinDecomposition A) := by
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
    exists_isometry_prod_pi_generators A hA
  choose p exp hp hexp hpk using fun i ↦ (isPrimePow_nat_iff (m i)).mp (hmθ i).1
  have hp_odd (i : Fin a) : Odd (p i) := by
    refine (hp i).odd_of_ne_two ?_
    intro h2
    have hm_odd := hm i
    rw [← hpk i, h2] at hm_odd
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero (hexp i).ne'
    rw [hj, pow_succ'] at hm_odd
    obtain ⟨t, ht⟩ := hm_odd
    omega
  let g₁ : Fin a → NikulinGenerator := fun i ↦ .oddCyclic (p i) (exp i) (hp i) (hp_odd i) (θ i)
  let g₂ : Fin b → NikulinGenerator := fun i ↦ .dyadicCyclic (k i + 1) (Nat.succ_pos _) (η i)
  let g₃ : Fin c → NikulinGenerator := fun i ↦ .dyadicU (ku i + 1)
  let g₄ : Fin d → NikulinGenerator := fun i ↦ .dyadicV (kv i + 1)
  have hg₁ (i : Fin a) : (g₁ i).IsAdmissible := by
    have hcop : IsCoprime (p i : ℤ) (θ i) := by
      have hpow : IsCoprime ((p i : ℤ) ^ exp i) (θ i) := by
        simpa only [← hpk i, Nat.cast_pow] using (hmθ i).2
      exact IsCoprime.of_isCoprime_of_dvd_left hpow (dvd_pow_self (p i : ℤ) (hexp i).ne')
    exact ⟨hexp i, ((Nat.prime_iff_prime_int.mp (hp i)).coprime_iff_not_dvd).mp hcop⟩
  let eOdd : Isometry (pi fun i ↦ oddCyclic (m i) (hm i) (θ i))
      (pi fun i ↦ (g₁ i).toFiniteQuadraticModule) :=
    QuadraticMap.IsometryEquiv.pi fun i ↦
      Isometry.ofEq (oddCyclic_congr (hpk i).symm (hm i) (hp_odd i).pow (θ i))
  let l₁ := List.ofFn g₁
  let l₂ := List.ofFn g₂
  let l₃ := List.ofFn g₃
  let l₄ := List.ofFn g₄
  let isoProd : Isometry
      ((pi fun i ↦ oddCyclic (m i) (hm i) (θ i)).prod
        ((pi fun i ↦ dyadicCyclic (k i + 1) (η i)).prod
          ((pi fun i ↦ dyadicU (ku i + 1)).prod (pi fun i ↦ dyadicV (kv i + 1)))))
      (orthogonalSumNikulinGenerators (l₁ ++ (l₂ ++ (l₃ ++ l₄)))) :=
    ((eOdd.trans (piToOrthogonalSumIsometry g₁)).prod
      ((piToOrthogonalSumIsometry g₂).prod
        (((piToOrthogonalSumIsometry g₃).prod (piToOrthogonalSumIsometry g₄)).trans
          (isometryOrthogonalSumAppend l₃ l₄).symm))).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod
          (isometryOrthogonalSumAppend l₂ (l₃ ++ l₄)).symm).trans
        (isometryOrthogonalSumAppend l₁ (l₂ ++ (l₃ ++ l₄))).symm)
  refine ⟨⟨l₁ ++ (l₂ ++ (l₃ ++ l₄)), ?_, f.symm.trans isoProd⟩⟩
  intro g hg
  simp only [l₁, l₂, l₃, l₄, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hg₁ i
  · exact hη i
  · exact Nat.succ_pos _
  · exact Nat.succ_pos _

/-- Every module admitting a Nikulin decomposition is nondegenerate. -/
theorem NikulinDecomposition.isNondegenerate {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) : A.IsNondegenerate :=
  D.isometry.isNondegenerate_iff.mpr <|
    (isNondegenerate_orthogonalSumNikulinGenerators_iff D.generators).mpr
      fun g hg ↦ (D.admissible g hg).isNondegenerate

/-- The cardinality of `A` is the product of the orders of the generators in `D`. -/
theorem NikulinDecomposition.natCard_eq {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) :
    Nat.card A = (D.generators.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod :=
  (Nat.card_congr D.isometry.toLinearEquiv.toEquiv).trans
    (natCard_orthogonalSumNikulinGenerators D.generators)

/-! ## Primary components and Nikulin's length formula -/

/-- The `p`-primary component of a finite quadratic module: `A.restrict` to
`AddCommGroup.primaryComponent A p`. -/
abbrev primaryComponent (A : FiniteQuadraticModule.{u}) (p : ℕ) : FiniteQuadraticModule.{u} :=
  A.restrict (AddCommGroup.primaryComponent A p)

/-- A quadratic isometry induces an isometry on `p`-primary components. -/
def Isometry.primaryComponentEquiv {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : Isometry A B) (p : ℕ) : Isometry (primaryComponent A p) (primaryComponent B p) where
  toLinearEquiv :=
    { toFun := fun x ↦ ⟨f x.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      invFun := fun y ↦ ⟨f.symm y.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      left_inv := fun x ↦ Subtype.ext (f.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (f.apply_symm_apply y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add f x.1 y.1)
      map_smul' := fun r x ↦ Subtype.ext (map_smul f r x.1) }
  map_app' x := f.map_app x.1

/-- Taking the `p`-primary component commutes with orthogonal products. -/
def primaryComponentProdIsometry (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v})
    (p : ℕ) :
    Isometry (primaryComponent (A.prod B) p)
      ((primaryComponent A p).prod (primaryComponent B p)) where
  toLinearEquiv :=
    { toFun := fun z ↦
        (⟨z.1.1, by
            obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp z.2
            exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.fst hk⟩⟩,
          ⟨z.1.2, by
            obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp z.2
            exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.snd hk⟩⟩)
      invFun := fun (xy : AddCommGroup.primaryComponent A p × AddCommGroup.primaryComponent B p) ↦
        ⟨((xy.1 : A), (xy.2 : B)), by
          obtain ⟨k₁, hk₁⟩ := AddCommGroup.mem_primaryComponent.mp xy.1.2
          obtain ⟨k₂, hk₂⟩ := AddCommGroup.mem_primaryComponent.mp xy.2.2
          have h1 : p ^ (k₁ + k₂) • (xy.1 : A) = 0 := by
            rw [pow_add, mul_nsmul, hk₁, nsmul_zero]
          have h2 : p ^ (k₁ + k₂) • (xy.2 : B) = 0 := by
            rw [pow_add, mul_comm, mul_nsmul, hk₂, nsmul_zero]
          exact AddCommGroup.mem_primaryComponent.mpr ⟨k₁ + k₂, Prod.ext h1 h2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_app' _ := rfl

private def primaryComponentGeneratorIsometry {g : NikulinGenerator} {p : ℕ} (hp : g.prime = p) :
    Isometry (primaryComponent g.toFiniteQuadraticModule p) g.toFiniteQuadraticModule where
  toLinearEquiv :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, hp ▸ g.mem_primaryComponent_prime x⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_app' _ := rfl

private theorem subsingleton_primaryComponent_of_prime_ne {g : NikulinGenerator} {p : ℕ}
    (hp : p.Prime) (hne : g.prime ≠ p) :
    Subsingleton (primaryComponent g.toFiniteQuadraticModule p) := by
  apply (Nat.card_eq_one_iff_unique.mp ?_).1
  rw [show Nat.card (primaryComponent g.toFiniteQuadraticModule p) =
      Nat.card (AddCommGroup.primaryComponent g.toFiniteQuadraticModule p) from rfl,
    TauCeti.AddCommGroup.natCard_primaryComponent _ hp]
  obtain ⟨n, hn⟩ := g.exists_pow_natCard
  have hndvd : ¬ p ∣ g.prime ^ n := fun hdvd ↦
    hne ((Nat.prime_dvd_prime_iff_eq hp g.prime_prime).mp (hp.dvd_of_dvd_pow hdvd)).symm
  rw [hn, Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]

/-- The `p`-primary component of an orthogonal sum of generators is isometric to the orthogonal sum
of the sublist of `p`-primary generators. -/
noncomputable def primaryComponentOrthogonalSumIsometry :
    ∀ (gs : List NikulinGenerator) {p : ℕ}, p.Prime →
      Isometry (primaryComponent (orthogonalSumNikulinGenerators gs) p)
        (orthogonalSumNikulinGenerators (gs.filter fun g ↦ g.prime = p))
  | [], p, _ => by
      simp only [List.filter_nil]
      have : Subsingleton (primaryComponent (orthogonalSumNikulinGenerators []) p) :=
        inferInstanceAs
          (Subsingleton (AddCommGroup.primaryComponent (orthogonalSumNikulinGenerators []) p))
      exact Isometry.ofSubsingleton
  | g :: gs, p, hp =>
      if h : g.prime = p then by
        simp only [List.filter_cons, h, decide_true]
        exact (primaryComponentProdIsometry _ _ p).trans
          ((primaryComponentGeneratorIsometry h).prod
            (primaryComponentOrthogonalSumIsometry gs hp))
      else by
        simp only [List.filter_cons, h, decide_false]
        have : Subsingleton (primaryComponent g.toFiniteQuadraticModule p) :=
          subsingleton_primaryComponent_of_prime_ne hp h
        exact (primaryComponentProdIsometry _ _ p).trans
          ((subsingletonProdIsometry _ _).trans (primaryComponentOrthogonalSumIsometry gs hp))

/-- Filtering a Nikulin decomposition by `g.prime = p` yields a Nikulin decomposition of the
`p`-primary component `primaryComponent A p`. -/
noncomputable def NikulinDecomposition.primaryComponent {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    NikulinDecomposition (FiniteQuadraticModule.primaryComponent A p) where
  generators := D.generators.filter fun g ↦ g.prime = p
  admissible _ hg := D.admissible _ (List.mem_of_mem_filter hg)
  isometry := (D.isometry.primaryComponentEquiv p).trans
    (primaryComponentOrthogonalSumIsometry D.generators hp)

@[simp]
theorem NikulinDecomposition.primaryComponent_generators {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    (D.primaryComponent hp).generators = D.generators.filter fun g ↦ g.prime = p :=
  (rfl)

/-- **Nikulin's `p`-primary length formula**: in any Nikulin decomposition `D` of `A`, the minimal
number of generators `l(A_p)` of `primaryComponent A p` equals the sum of the realization ranks of
the `p`-primary generators of `D`. -/
theorem NikulinDecomposition.rank_primaryComponent {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (FiniteQuadraticModule.primaryComponent A p) =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  have heq := AddGroup.rank_congr (D.primaryComponent hp).isometry.toLinearEquiv.toAddEquiv
  rw [heq, NikulinDecomposition.primaryComponent_generators]
  exact rank_orthogonalSumNikulinGenerators_eq_sum_of_prime hp
    (fun g hg ↦ D.admissible g (List.mem_of_mem_filter hg))
    (fun g hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2)

/-- **Nikulin's global length formula**: in any Nikulin decomposition `D` of `A`, the minimal
number of generators `l(A)` equals the supremum over `p ∣ #A` of the total realization rank of the
`p`-primary generators of `D`. -/
theorem NikulinDecomposition.rank_eq_sup_filter {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) :
    AddGroup.rank A =
      (Nat.card A).primeFactors.sup fun p ↦
        ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  rw [AddGroup.rank_eq_sup_primaryComponents A]
  apply le_antisymm
  · refine Finset.sup_le fun p _ ↦ ?_
    -- Identify `AddCommGroup.primaryComponent A p.1` with the carrier of `primaryComponent A p.1`.
    change AddGroup.rank (FiniteQuadraticModule.primaryComponent A p.1) ≤ _
    rw [D.rank_primaryComponent (Nat.prime_of_mem_primeFactors p.2)]
    exact Finset.le_sup
      (f := fun q ↦ ((D.generators.filter fun g ↦ g.prime = q).map NikulinGenerator.rank).sum) p.2
  · refine Finset.sup_le fun p hp ↦ ?_
    rw [← D.rank_primaryComponent (Nat.prime_of_mem_primeFactors hp)]
    exact Finset.le_sup (f := fun q : (Nat.card A).primeFactors ↦
      AddGroup.rank (AddCommGroup.primaryComponent A q.1)) (Finset.mem_univ ⟨p, hp⟩)

/-! ## Cyclic summands of order `2` -/

/-- **The dyadic alternative of Nikulin's Theorems 1.9.1 and 1.10.1**: `A` splits off an orthogonal
summand `q_θ^{(2)}(2)` with `θ` odd. -/
@[expose] def HasCyclicTwoSummand (A : FiniteQuadraticModule.{u}) : Prop :=
  ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
    Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A'))

/-- `HasCyclicTwoSummand` is invariant under quadratic isometry. -/
theorem Isometry.hasCyclicTwoSummand_iff {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) :
    HasCyclicTwoSummand A ↔ HasCyclicTwoSummand B := by
  refine ⟨fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.symm.trans g⟩⟩,
    fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.trans g⟩⟩⟩

/-- Any generator `q_θ^{(2)}(2)` (`θ` odd) satisfies `HasCyclicTwoSummand`. -/
theorem hasCyclicTwoSummand_dyadicCyclic_one {θ : ℤ} (hθ : Odd θ) :
    HasCyclicTwoSummand (dyadicCyclic 1 θ) :=
  ⟨θ, orthogonalSumNikulinGenerators [], hθ,
    ⟨(subsingletonProdIsometry (orthogonalSumNikulinGenerators []) (dyadicCyclic 1 θ)).symm.trans
      (QuadraticMap.IsometryEquiv.prodComm _ _)⟩⟩

/-- If a Nikulin decomposition of `A` contains a generator `.dyadicCyclic 1 _ θ`, then `A` has a
cyclic summand of order `2`. -/
theorem NikulinDecomposition.hasCyclicTwoSummand_of_mem {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {hk : 0 < 1} {θ : ℤ}
    (hmem : NikulinGenerator.dyadicCyclic 1 hk θ ∈ D.generators) :
    HasCyclicTwoSummand A := by
  have hθ : Odd θ := D.admissible _ hmem
  obtain ⟨gs', ⟨e⟩⟩ := exists_orthogonalSum_of_mem hmem
  exact ⟨θ, orthogonalSumNikulinGenerators gs', hθ, ⟨D.isometry.trans e⟩⟩

/-- A module of odd order has no cyclic summand of order `2`. -/
theorem not_hasCyclicTwoSummand_of_odd_natCard {A : FiniteQuadraticModule.{u}}
    (hodd : Odd (Nat.card A)) : ¬ HasCyclicTwoSummand A := by
  rintro ⟨θ, A', -, ⟨f⟩⟩
  have hc := Nat.card_congr f.toLinearEquiv.toEquiv
  rw [Nat.card_prod, natCard_dyadicCyclic, pow_one] at hc
  rw [hc] at hodd
  obtain ⟨t, ht⟩ := hodd
  omega

end TauCeti.FiniteQuadraticModule
