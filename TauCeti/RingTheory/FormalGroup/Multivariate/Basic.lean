/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Commutative formal Lie groups in coordinates

A law of dimension `n` over `R` has one power series per output coordinate and two blocks
of `n` input variables. The unit, symmetry and associativity identities are identities in
the universal variables. They can therefore be used after any admissible formal substitution,
including substitutions with nilpotent constant coefficients.

We use the coordinate description of Stix, *A course on finite flat group schemes*, §10.2.2.
The transport of the unit, symmetry and associativity identities generalizes the one-dimensional
substitution arguments in Mathlib's `FormalGroup.add_zero`, `FormalGroup.comm'` and
`FormalGroup.assoc'`.
-/

public section

noncomputable section

namespace TauCeti

open MvPowerSeries

variable {R : Type*} [CommRing R] {n : ℕ} {σ : Type*}

/-- A commutative formal Lie group of dimension `n` in a chosen system of parameters.
The first variable index chooses the input block and the second chooses a coordinate. -/
structure FormalLieGroup (R : Type*) [CommRing R] (n : ℕ) where
  /-- The coordinate series of the group law. -/
  law : Fin n → MvPowerSeries (Fin 2 × Fin n) R
  /-- The origin is a right unit. -/
  right_unit : substLaw law (X (R := R)) 0 = X
  /-- The two input blocks can be exchanged. -/
  comm : substLaw law (fun i ↦ X (R := R) ((0 : Fin 2), i)) (fun i ↦ X (1, i)) =
    substLaw law (fun i ↦ X (1, i)) (fun i ↦ X (0, i))
  /-- The two bracketings agree in three blocks of independent variables. -/
  assoc :
    let x := fun i : Fin n ↦ X (R := R) ((0 : Fin 3), i)
    let y := fun i : Fin n ↦ X (R := R) ((1 : Fin 3), i)
    let z := fun i : Fin n ↦ X (R := R) ((2 : Fin 3), i)
    substLaw law (substLaw law x y) z = substLaw law x (substLaw law y z)

namespace FormalLieGroup

@[ext]
theorem ext {F G : FormalLieGroup R n} (h : F.law = G.law) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (F : FormalLieGroup R n) {S : Type*} [CommRing S] [Algebra R S]

/-- The right unit identity on admissible tuples. -/
@[simp]
theorem substLaw_zero_right {x : Fin n → MvPowerSeries σ S} (hx : HasSubst x) :
    substLaw F.law x 0 = x := by
  funext i
  have h := congrArg (subst x) (congrFun F.right_unit i)
  have hz : HasSubst (0 : Fin n → MvPowerSeries (Fin n) R) := HasSubst.zero
  have h0 : subst x (0 : MvPowerSeries (Fin n) R) = 0 := by
    rw [← substAlgHom_apply hx, map_zero]
  -- The transport produces a lambda-valued zero tuple. Expose the target's zero tuple too,
  -- since Pi.zero_apply simplifies applied zeros, not a zero tuple passed to substLaw.
  change substLaw F.law x (fun _ ↦ 0) i = x i
  simpa only [subst_substLaw _ HasSubst.X hz hx, subst_X hx, Pi.zero_apply, h0] using h

/-- Symmetry of the formal sum on admissible tuples. -/
theorem substLaw_comm {x y : Fin n → MvPowerSeries σ S} (hx : HasSubst x) (hy : HasSubst y) :
    substLaw F.law x y = substLaw F.law y x := by
  let a := ![x, y]
  have a₀ : a 0 = x := by simp [a]
  have a₁ : a 1 = y := by simp [a]
  have ha : HasSubst (Function.uncurry a) := hx.pair hy
  funext i
  have h := congrArg (subst (Function.uncurry a)) (congrFun F.comm i)
  simpa only [subst_substLaw_X_blocks _ ha, a₀, a₁] using h

/-- The left unit identity on admissible tuples. -/
@[simp]
theorem substLaw_zero_left {x : Fin n → MvPowerSeries σ S} (hx : HasSubst x) :
    substLaw F.law 0 x = x := by
  exact (F.substLaw_comm (x := 0) HasSubst.zero hx).trans (F.substLaw_zero_right hx)

private def blockEmbedding (b : Fin 2) : Fin n ↪ Fin 2 × Fin n :=
  ⟨fun j ↦ (b, j), Prod.mk_right_injective b⟩

open WithPiTopology in
private theorem killCompl_block_eq_subst (b : Fin 2) (f : MvPowerSeries (Fin 2 × Fin n) R) :
    killCompl (blockEmbedding b) f = f.subst
      (fun k ↦ if k.1 = b then X k.2 else 0) := by
  let e : Fin n ↪ Fin 2 × Fin n := blockEmbedding b
  let a (k : Fin 2 × Fin n) : MvPowerSeries (Fin n) R := if k.1 = b then X k.2 else 0
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun k ↦
    by simp [a, apply_ite constantCoeff]
  have hX (k : Fin 2 × Fin n) : killCompl e (X (R := R) k) = a k := by
    rcases k with ⟨c, j⟩
    by_cases h : c = b
    · subst c
      have he : e j = (b, j) := rfl
      simpa only [he, a, ite_true] using (killCompl_X (R := R) (e := e) j)
    · simp only [a, h, ite_false]
      apply killCompl_X_eq_zero
      rintro ⟨l, hl⟩
      exact h (congrArg Prod.fst hl).symm
  let : UniformSpace R := ⊥
  let : DiscreteUniformity R := ⟨rfl⟩
  have hc : Continuous (killCompl (R := R) e) := by
    apply continuous_pi
    intro d
    change Continuous (fun g ↦ coeff d (killCompl e g))
    simp only [coeff_killCompl]
    exact continuous_coeff R _
  have hs : Continuous (substAlgHom (R := R) ha) := by
    simpa only [coe_substAlgHom] using (continuous_subst (R := R) ha)
  have h : (aeval (HasEval.X.map hc) : MvPowerSeries (Fin 2 × Fin n) R →ₐ[R]
      MvPowerSeries (Fin n) R) = aeval (HasEval.X.map hs) := by
    apply DFunLike.ext'
    simp only [coe_aeval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, substAlgHom_X, hX]
  simpa only [substAlgHom_apply] using
    DFunLike.congr_fun ((aeval_unique hc).symm.trans (h.trans (aeval_unique hs))) f

/-- The coefficients supported in one input block are those of the corresponding variable. -/
theorem coeff_embDomain_law (b : Fin 2) (d : Fin n →₀ ℕ) (i : Fin n) :
    coeff (Finsupp.embDomain (⟨fun j ↦ (b, j), Prod.mk_right_injective b⟩ :
      Fin n ↪ Fin 2 × Fin n) d) (F.law i) = coeff d (X i) := by
  change coeff (Finsupp.embDomain (blockEmbedding b) d) (F.law i) = _
  rw [← coeff_killCompl, killCompl_block_eq_subst]
  congr 1
  fin_cases b
  · convert congrFun F.right_unit i using 1
    rw [substLaw_def]
    congr 1
    funext ⟨k, j⟩
    fin_cases k <;> simp [Function.uncurry]
  · convert congrFun (F.substLaw_zero_left (HasSubst.X (S := R))) i using 1
    rw [substLaw_def]
    congr 1
    funext ⟨k, j⟩
    fin_cases k <;> simp [Function.uncurry]

/-- Every coordinate of a formal Lie group law vanishes at the origin. -/
@[simp]
theorem constantCoeff_law (i : Fin n) : constantCoeff (F.law i) = 0 := by
  simpa [Finsupp.embDomain_zero, coeff_zero_eq_constantCoeff_apply] using
    F.coeff_embDomain_law 0 0 i

/-- The linear part in either input block is the identity matrix. -/
@[simp]
theorem coeff_single_law (b : Fin 2) (j i : Fin n) :
    coeff (Finsupp.single (b, j) 1) (F.law i) = if j = i then 1 else 0 := by
  simpa [Finsupp.embDomain_single, coeff_X, Finsupp.single_left_inj one_ne_zero] using
    F.coeff_embDomain_law b (Finsupp.single j 1) i

/-- A formal sum of admissible tuples is admissible. -/
theorem hasSubst_substLaw {x y : Fin n → MvPowerSeries σ S} (hx : HasSubst x)
    (hy : HasSubst y) : HasSubst (substLaw F.law x y) :=
  hasSubst_of_constantCoeff_nilpotent fun i ↦ by
    rw [substLaw_def]
    exact IsNilpotent_subst (hx.pair hy) (F.constantCoeff_law i ▸ IsNilpotent.zero)

/-- Associativity of the formal sum on admissible tuples. -/
theorem substLaw_assoc {x y z : Fin n → MvPowerSeries σ S}
    (hx : HasSubst x) (hy : HasSubst y) (hz : HasSubst z) :
    substLaw F.law (substLaw F.law x y) z = substLaw F.law x (substLaw F.law y z) := by
  let a := ![x, y, z]
  have a₀ : a 0 = x := by simp [a]
  have a₁ : a 1 = y := by simp [a]
  have a₂ : a 2 = z := by simp [a]
  -- To prove admissibility of the three blocks, separate the first block from the remaining two.
  have ha : HasSubst (Function.uncurry a) :=
    .uncurry (Fin.forall_fin_succ.mpr ⟨hx, Fin.forall_fin_two.mpr ⟨hy, hz⟩⟩)
  have hb (b : Fin 3) : HasSubst (fun j : Fin n ↦ X (R := R) (b, j)) := HasSubst.X.curry b
  have hxy := F.hasSubst_substLaw (S := R) (hb 0) (hb 1)
  have hyz := F.hasSubst_substLaw (S := R) (hb 1) (hb 2)
  funext i
  have h := congrArg (subst (Function.uncurry a)) (congrFun F.assoc i)
  simpa only [subst_substLaw _ hxy (hb 2) ha,
    subst_substLaw _ (hb 0) hyz ha, subst_substLaw_X_blocks _ ha,
    subst_X ha, Function.uncurry_apply_pair, a₀, a₁, a₂] using h

private theorem substLaw_additive_raw (R : Type*) [CommRing R] [Algebra R S]
    (x y : Fin n → MvPowerSeries σ S) :
    substLaw (fun i ↦ X (R := R) ((0 : Fin 2), i) + X (1, i)) x y = x + y := by
  funext i
  simp [substLaw_def, Function.uncurry]

/-- The additive formal Lie group in `n` coordinates, with coordinatewise addition. -/
def additive (R : Type*) [CommRing R] (n : ℕ) : FormalLieGroup R n where
  law i := X ((0 : Fin 2), i) + X (1, i)
  right_unit := by simp only [substLaw_additive_raw, add_zero]
  comm := by simp only [substLaw_additive_raw, add_comm]
  assoc := by
    dsimp only
    simp only [substLaw_additive_raw, add_assoc]

@[simp]
theorem additive_law (i : Fin n) :
    (additive R n).law i = X ((0 : Fin 2), i) + X (1, i) := (rfl)

/-- The additive formal Lie group sums arbitrary tuples coordinatewise. -/
@[simp]
theorem substLaw_additive (x y : Fin n → MvPowerSeries σ S) :
    substLaw (additive R n).law x y = x + y :=
  substLaw_additive_raw R x y

end FormalLieGroup

end TauCeti
