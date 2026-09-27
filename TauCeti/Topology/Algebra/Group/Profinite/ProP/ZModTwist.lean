/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.MulCastHom
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# The twisted coefficients `I(χ)/pⁱ` of a `p`-adic character

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character. For each `i`, the
finite discrete module `I(χ)/pⁱ` is `ℤ/pⁱ` with `G` acting by `g • x = χ(g) x`, the action being
through the truncation `charScalar χ i g` of `χ g` modulo `pⁱ`. The reductions
`I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i` are equivariant and surjective, and form a compatible system.
Dually, multiplication by `pʲ` is an equivariant injection `I(χ)/pⁱ → I(χ)/pⁱ⁺ʲ`, and the two fit
into the short exact sequences

```text
0 → I(χ)/pⁱ → I(χ)/pⁱ⁺ʲ → I(χ)/pʲ → 0
```

of discrete `G`-modules, whose long exact cohomology sequences relate the cohomology of the levels.
These are the coefficient modules of Labute's prescription property of a character and of the
twisted duality `M^∨(χ) = Hom(M, I(χ)/pⁱ)`.

The coefficient module is placed in the universe of `G`, as a structure wrapping `ZMod (p ^ i)`,
because the universal property of a free pro-`p` group lifts maps into groups of the universe of
its generators. `I(χ)/p` is `ZModTwist χ 1`, the module at `i = 1`, with carrier `ZMod (p ^ 1)`.

## Main definitions

* `TauCeti.charScalar`: the scalar `χ g mod pⁱ` by which `g` acts, as a monoid homomorphism
  `G →* ZMod (p ^ i)`.
* `TauCeti.ZModTwist`: the twisted module `I(χ)/pⁱ`, a finite discrete `G`-module with continuous
  action; `TauCeti.ZModTwist.equiv` identifies it additively with `ZMod (p ^ i)`.
* `TauCeti.ZModTwist.reduce`: the equivariant reduction `I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i`, with
  `TauCeti.ZModTwist.reduce_self` and `TauCeti.ZModTwist.reduce_reduce` its identity and
  composition laws.
* `TauCeti.ZModTwist.mulPow`: the equivariant multiplication by `pʲ`, `I(χ)/pⁱ → I(χ)/pⁿ` for
  `i + j = n`, with `TauCeti.ZModTwist.mulPow_zero` and `TauCeti.ZModTwist.mulPow_mulPow` its
  identity and composition laws.
* `TauCeti.ZModTwist.shortExact`: the short exact sequence `0 → I(χ)/pⁱ → I(χ)/pⁿ → I(χ)/pʲ → 0`
  of discrete `G`-modules, for `i + j = n`.

## Main results

* `TauCeti.ZModTwist.isProP_multiplicative`: `I(χ)/pⁱ` is pro-`p`.
* `TauCeti.ZModTwist.reduce_surjective`: the reductions are surjective.
* `TauCeti.ZModTwist.mulPow_injective`: the multiplications are injective.
* `TauCeti.ZModTwist.reduce_mulPow_eq_mulPow_reduce`: the reductions commute with the
  multiplications, and `TauCeti.ZModTwist.explicitCoeff1_reduce_explicitCoeff1_mulPow` is the
  induced commutation on `H¹`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The scalar of the action -/

/-- The scalar by which `g` acts on `I(χ)/pⁱ`: the truncation of `χ g` modulo `pⁱ`, as a monoid
homomorphism into the multiplicative monoid of `ZMod (p ^ i)`. -/
noncomputable def charScalar (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) : G →* ZMod (p ^ i) :=
  ((PadicInt.toZModPow i : ℤ_[p] →+* ZMod (p ^ i)) : ℤ_[p] →* ZMod (p ^ i)).comp
    ((Units.coeHom ℤ_[p]).comp χ.toMonoidHom)

variable (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)

/-- The scalar of the action of `g` is the truncation of `χ g` modulo `pⁱ`. -/
@[simp]
theorem charScalar_apply (g : G) : charScalar χ i g = PadicInt.toZModPow i (χ g : ℤ_[p]) :=
  (rfl)

/-- The scalar of the action depends continuously on the group element, because `χ` and the
truncation modulo `pⁱ` are continuous. -/
theorem continuous_charScalar : Continuous (charScalar χ i) :=
  (PadicInt.continuous_toZModPow i).comp (Units.continuous_val.comp χ.continuous)

/-- The scalar of the action is a unit, being the reduction of a `p`-adic unit. -/
theorem isUnit_charScalar (g : G) : IsUnit (charScalar χ i g) :=
  (χ g).isUnit.map (PadicInt.toZModPow i)

variable {i}

-- Not `@[simp]`: Mathlib's simp lemma `ZMod.castHom_apply` rewrites the left-hand side to
-- `(charScalar χ i g).cast` first, so the tagged lemma fails the `simpNF` linter.
/-- The scalars at different levels are compatible under reduction: the scalar at level `i`
reduces modulo `pʲ` to the scalar at level `j ≤ i`. -/
theorem castHom_charScalar {j : ℕ} (h : j ≤ i) (g : G) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) (charScalar χ i g) = charScalar χ j g :=
  RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow j i h) _

variable (i)

/-! ### The twisted module -/

/-- **The twisted module `I(χ)/pⁱ`**: the additive group `ZMod (p ^ i)`, placed in the universe of
`G`, on which `g` acts by multiplication by the scalar `charScalar χ i g`. The character is a
parameter of the type so that the action can be an instance. -/
@[ext]
structure ZModTwist (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) : Type u where
  /-- The underlying residue class modulo `pⁱ`. -/
  val : ZMod (p ^ i)

namespace ZModTwist

instance : AddCommGroup (ZModTwist χ i) :=
  Equiv.addCommGroup ⟨val, mk, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The identification of `I(χ)/pⁱ` with `ZMod (p ^ i)` as an additive group, forgetting the
action. -/
def equiv : ZModTwist χ i ≃+ ZMod (p ^ i) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem equiv_apply (x : ZModTwist χ i) : equiv χ i x = x.val := (rfl)

@[simp] theorem equiv_symm_apply (x : ZMod (p ^ i)) : (equiv χ i).symm x = ⟨x⟩ := (rfl)

@[simp] theorem val_zero : (0 : ZModTwist χ i).val = 0 := (rfl)

@[simp] theorem val_add (x y : ZModTwist χ i) : (x + y).val = x.val + y.val := (rfl)

@[simp] theorem val_neg (x : ZModTwist χ i) : (-x).val = -x.val := (rfl)

@[simp] theorem val_sub (x y : ZModTwist χ i) : (x - y).val = x.val - y.val := (rfl)

instance : TopologicalSpace (ZModTwist χ i) := ⊥

instance : DiscreteTopology (ZModTwist χ i) := ⟨rfl⟩

instance : Finite (ZModTwist χ i) := Finite.of_equiv _ (equiv χ i).symm.toEquiv

/-- `G` acts on `I(χ)/pⁱ` through the scalar `charScalar χ i`. -/
noncomputable instance : SMul G (ZModTwist χ i) where
  smul g x := ⟨charScalar χ i g * x.val⟩

@[simp]
theorem val_smul (g : G) (x : ZModTwist χ i) : (g • x).val = charScalar χ i g * x.val :=
  (rfl)

/-- The action of `G` on `I(χ)/pⁱ` through the scalar `charScalar χ i` is distributive. -/
noncomputable instance : DistribMulAction G (ZModTwist χ i) where
  one_smul x := ZModTwist.ext (by simp)
  mul_smul g h x := ZModTwist.ext (by simp [mul_assoc])
  smul_zero g := ZModTwist.ext (by simp)
  smul_add g x y := ZModTwist.ext (by simp [mul_add])

/-- The action of `G` on the discrete module `I(χ)/pⁱ` is continuous, because the scalar
`charScalar χ i` is. -/
instance : ContinuousSMul G (ZModTwist χ i) where
  continuous_smul :=
    (continuous_of_discreteTopology (f := fun q : ZMod (p ^ i) × ZModTwist χ i ↦
      (⟨q.1 * q.2.val⟩ : ZModTwist χ i))).comp
      (((continuous_charScalar χ i).comp continuous_fst).prodMk continuous_snd)

/-- `I(χ)/pⁱ`, with its discrete topology, is pro-`p`: it is the discrete cyclic group `ℤ/pⁱ`. -/
theorem isProP_multiplicative : IsProP p (Multiplicative (ZModTwist χ i)) :=
  (isProP_multiplicative_zmod_pow p i).of_equiv
    ⟨AddEquiv.toMultiplicative (equiv χ i).symm, continuous_of_discreteTopology,
      continuous_of_discreteTopology⟩

variable {i}

/-- **The reduction `I(χ)/pⁱ → I(χ)/pʲ`** for `j ≤ i`, an equivariant additive homomorphism. -/
def reduce {j : ℕ} (h : j ≤ i) : ZModTwist χ i →+[G] ZModTwist χ j where
  toFun x := ⟨ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) x.val⟩
  map_smul' g x :=
    ZModTwist.ext (by simp only [val_smul, map_mul, castHom_charScalar χ h, MonoidHom.id_apply])
  map_zero' := ZModTwist.ext (by simp only [val_zero, map_zero])
  map_add' x y := ZModTwist.ext (by simp only [val_add, map_add])

@[simp]
theorem val_reduce {j : ℕ} (h : j ≤ i) (x : ZModTwist χ i) :
    (reduce χ h x).val = ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) x.val :=
  (rfl)

/-- The reduction from a level to itself is the identity. -/
@[simp]
theorem reduce_self (x : ZModTwist χ i) : reduce χ le_rfl x = x :=
  ZModTwist.ext (by rw [val_reduce, ZMod.castHom_self, RingHom.id_apply])

/-- Two successive reductions compose to the reduction between the outer levels. -/
@[simp]
theorem reduce_reduce {j k : ℕ} (h₁ : j ≤ i) (h₂ : k ≤ j) (x : ZModTwist χ i) :
    reduce χ h₂ (reduce χ h₁ x) = reduce χ (h₂.trans h₁) x :=
  ZModTwist.ext (RingHom.congr_fun (ZMod.castHom_comp (pow_dvd_pow p h₂) (pow_dvd_pow p h₁)) _)

/-- The reduction `I(χ)/pⁱ → I(χ)/pʲ` is surjective: every residue class modulo `pʲ` lifts to a
residue class modulo `pⁱ`. -/
theorem reduce_surjective {j : ℕ} (h : j ≤ i) : Function.Surjective (reduce χ h) := fun y ↦ by
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow p h) y.val
  exact ⟨⟨x⟩, ZModTwist.ext hx⟩

/-! ### The trivial module at level zero -/

/-- `I(χ)/p⁰ = ℤ/1` is trivial. -/
instance : Subsingleton (ZModTwist χ 0) :=
  have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
  (equiv χ 0).toEquiv.subsingleton

/-! ### Multiplication by `pʲ` -/

variable {j n : ℕ}

/-- **Multiplication by `pʲ`, `I(χ)/pⁱ →+[G] I(χ)/pⁿ`** for `i + j = n`. It is equivariant because
the scalar of the action at level `n` reduces to the scalar at level `i`. -/
def mulPow (h : i + j = n) : ZModTwist χ i →+[G] ZModTwist χ n where
  toFun x := ⟨ZMod.mulCastHom (p ^ j) ((pow_add p i j).symm.trans (congrArg (p ^ ·) h)) x.val⟩
  map_smul' g x := ZModTwist.ext (by
    simp only [val_smul, MonoidHom.id_apply]
    rw [← castHom_charScalar χ (Nat.le.intro h) g, ZMod.mulCastHom_castHom_mul])
  map_zero' := ZModTwist.ext (by simp only [val_zero, map_zero])
  map_add' _ _ := ZModTwist.ext (by simp only [val_add, map_add])

/-- The residue class of `pʲ x` is `pʲ` times the residue class of `x`. -/
@[simp]
theorem val_mulPow (h : i + j = n) (x : ZModTwist χ i) :
    (mulPow χ h x).val =
      ZMod.mulCastHom (p ^ j) ((pow_add p i j).symm.trans (congrArg (p ^ ·) h)) x.val :=
  (rfl)

/-- Multiplication by `pʲ` is injective on `I(χ)/pⁱ`. -/
theorem mulPow_injective (h : i + j = n) : Function.Injective (mulPow χ h) := fun _ _ hxy ↦
  ZModTwist.ext
    (ZMod.mulCastHom_injective _ _ (pow_ne_zero j (Fact.out : p.Prime).ne_zero) (congrArg val hxy))

/-- Multiplication by `p⁰` is the identity. -/
@[simp]
theorem mulPow_zero : mulPow χ (Nat.add_zero i) = DistribMulActionHom.id G :=
  DistribMulActionHom.ext fun x ↦ ZModTwist.ext <| by
    simp only [val_mulPow, DistribMulActionHom.id_apply, pow_zero, ZMod.mulCastHom_one,
      AddMonoidHom.id_apply]

/-- Two successive multiplications, by `pʲ` and then by `pᵏ`, compose to the multiplication by
`pʲ⁺ᵏ`. The index equation of the composite is taken as a hypothesis, so that any proof of it may
be used. -/
theorem mulPow_mulPow {k m : ℕ} (h : i + j = n) (h' : n + k = m) (h'' : i + (j + k) = m)
    (x : ZModTwist χ i) : mulPow χ h' (mulPow χ h x) = mulPow χ h'' x :=
  ZModTwist.ext <| by
    rw [val_mulPow, val_mulPow, val_mulPow,
      ZMod.mulCastHom_mulCastHom _ _ _ _ (by rw [← pow_add, ← pow_add, h''])]
    simp only [pow_add]

/-- The reduction modulo `pʲ` kills the image of the multiplication by `pʲ`. -/
@[simp]
theorem reduce_mulPow (h : i + j = n) (x : ZModTwist χ i) :
    reduce χ (Nat.le.intro ((Nat.add_comm j i).trans h)) (mulPow χ h x) = 0 :=
  ZModTwist.ext (ZMod.castHom_mulCastHom _ _ x.val)

/-- The reductions commute with the multiplications: reducing `pʲ x` from level `n` to level `n'`
is `pʲ` times the reduction of `x` from level `i` to level `i'`, when `i + j = n` and
`i' + j = n'`. -/
theorem reduce_mulPow_eq_mulPow_reduce {i' n' : ℕ} (h : i + j = n) (h' : i' + j = n') (hi : i' ≤ i)
    (hn : n' ≤ n) (x : ZModTwist χ i) :
    reduce χ hn (mulPow χ h x) = mulPow χ h' (reduce χ hi x) :=
  ZModTwist.ext (ZMod.castHom_mulCastHom_eq_mulCastHom_castHom _ _ _ _ _ x.val)

/-- Two successive reductions compose to the reduction between the outer levels, as equivariant
homomorphisms. -/
theorem reduce_comp_reduce {j k : ℕ} (h₁ : j ≤ i) (h₂ : k ≤ j) :
    (reduce χ h₂).comp (reduce χ h₁) = reduce χ (h₂.trans h₁) :=
  DistribMulActionHom.ext (reduce_reduce χ h₁ h₂)

/-- `reduce_mulPow_eq_mulPow_reduce`, as an equality of equivariant homomorphisms. -/
theorem reduce_comp_mulPow {i' n' : ℕ} (h : i + j = n) (h' : i' + j = n') (hi : i' ≤ i)
    (hn : n' ≤ n) : (reduce χ hn).comp (mulPow χ h) = (mulPow χ h').comp (reduce χ hi) :=
  DistribMulActionHom.ext (reduce_mulPow_eq_mulPow_reduce χ h h' hi hn)

/-! ### The short exact sequences `0 → I(χ)/pⁱ → I(χ)/pⁱ⁺ʲ → I(χ)/pʲ → 0` -/

open ContCohomology

/-- **The short exact sequence `0 → I(χ)/pⁱ → I(χ)/pⁿ → I(χ)/pʲ → 0`** of discrete `G`-modules, for
`i + j = n`: multiplication by `pʲ` followed by reduction modulo `pʲ`. -/
def shortExact (h : i + j = n) :
    DiscreteShortExact G (ZModTwist χ i) (ZModTwist χ n) (ZModTwist χ j) where
  incl := mulPow χ h
  proj := reduce χ (Nat.le.intro ((Nat.add_comm j i).trans h))
  incl_equivariant := (mulPow χ h).map_smul
  proj_equivariant := (reduce χ (Nat.le.intro ((Nat.add_comm j i).trans h))).map_smul
  incl_injective := mulPow_injective χ h
  proj_surjective := reduce_surjective χ (Nat.le.intro ((Nat.add_comm j i).trans h))
  exact y := by
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := (ZMod.exact_mulCastHom_castHom (p ^ j)
        ((pow_add p i j).symm.trans (congrArg (p ^ ·) h)) y.val).1 (congrArg val hy)
      exact ⟨⟨a⟩, ZModTwist.ext ha⟩
    · rintro ⟨x, rfl⟩
      exact ZModTwist.ext (ZMod.castHom_mulCastHom _ _ x.val)

/-- The inclusion of `shortExact` multiplies by `pʲ`. -/
@[simp]
theorem shortExact_incl_apply (h : i + j = n) (x : ZModTwist χ i) :
    (shortExact χ h).incl x = mulPow χ h x :=
  congrFun (DistribMulActionHom.coe_fn_coe (mulPow χ h)) x

/-- The projection of `shortExact` reduces modulo `pʲ`. -/
@[simp]
theorem shortExact_proj_apply (h : i + j = n) (y : ZModTwist χ n) :
    (shortExact χ h).proj y = reduce χ (Nat.le.intro ((Nat.add_comm j i).trans h)) y :=
  congrFun (DistribMulActionHom.coe_fn_coe (reduce χ _)) y

/-- The inclusion of `shortExact` is the multiplication by `pʲ`. -/
theorem shortExact_inclDistribMulActionHom (h : i + j = n) :
    (shortExact χ h).inclDistribMulActionHom = mulPow χ h :=
  DistribMulActionHom.ext fun x ↦
    ((shortExact χ h).inclDistribMulActionHom_apply x).trans (shortExact_incl_apply χ h x)

/-- The projection of `shortExact` is the reduction modulo `pʲ`. -/
theorem shortExact_projDistribMulActionHom (h : i + j = n) :
    (shortExact χ h).projDistribMulActionHom =
      reduce χ (Nat.le.intro ((Nat.add_comm j i).trans h)) :=
  DistribMulActionHom.ext fun y ↦
    ((shortExact χ h).projDistribMulActionHom_apply y).trans (shortExact_proj_apply χ h y)

/-! ### The induced maps on `H¹`

The reductions and multiplications induce maps on the explicit first continuous cohomology, and
their composition laws pass to those maps. Both continuity proofs are the generic
`continuous_of_discreteTopology`, which is what lets an equality of coefficient maps be transported
across `explicitCoeff1` by `congrArg`. -/

/-- Two successive reductions on `H¹` compose to the reduction between the outer levels. -/
theorem explicitCoeff1_reduce_explicitCoeff1_reduce {j k : ℕ} (h₁ : j ≤ i) (h₂ : k ≤ j)
    (x : H1 G (ZModTwist χ i)) :
    explicitCoeff1 G (ZModTwist χ j) (reduce χ h₂) continuous_of_discreteTopology
        (explicitCoeff1 G (ZModTwist χ i) (reduce χ h₁) continuous_of_discreteTopology x) =
      explicitCoeff1 G (ZModTwist χ i) (reduce χ (h₂.trans h₁))
        continuous_of_discreteTopology x := by
  rw [← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
  exact congrArg (fun f : ZModTwist χ i →+[G] ZModTwist χ k ↦
    explicitCoeff1 G (ZModTwist χ i) f continuous_of_discreteTopology x)
    (reduce_comp_reduce χ h₁ h₂)

/-- On `H¹`, reducing after multiplying by `pʲ` is multiplying by `pʲ` after reducing. -/
theorem explicitCoeff1_reduce_explicitCoeff1_mulPow {i' n' : ℕ} (h : i + j = n) (h' : i' + j = n')
    (hi : i' ≤ i) (hn : n' ≤ n) (x : H1 G (ZModTwist χ i)) :
    explicitCoeff1 G (ZModTwist χ n) (reduce χ hn) continuous_of_discreteTopology
        (explicitCoeff1 G (ZModTwist χ i) (mulPow χ h) continuous_of_discreteTopology x) =
      explicitCoeff1 G (ZModTwist χ i') (mulPow χ h') continuous_of_discreteTopology
        (explicitCoeff1 G (ZModTwist χ i) (reduce χ hi) continuous_of_discreteTopology x) := by
  rw [← AddMonoidHom.comp_apply, ← explicitCoeff1_comp, ← AddMonoidHom.comp_apply,
    ← explicitCoeff1_comp]
  exact congrArg (fun f : ZModTwist χ i →+[G] ZModTwist χ n' ↦
    explicitCoeff1 G (ZModTwist χ i) f continuous_of_discreteTopology x)
    (reduce_comp_mulPow χ h h' hi hn)

end ZModTwist

end TauCeti
