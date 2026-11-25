/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension

/-!
# Extension of scalars of right modules over noncommutative rings

For a ring homomorphism `f : R →+* S` of possibly noncommutative rings and a right `R`-module
`P`, encoded as a left `Rᵐᵒᵖ`-module, the extension of scalars `P ⊗_R S` is the balanced tensor
product of `P` with `S`, regarded as a left `R`-module through `r · s = f r * s`. It is the
quotient of `P ⊗[ℤ] S` by the balancing relations `(p · r) ⊗ s = p ⊗ (f r * s)`, and `S` acts on
the right through the second factor: `(p ⊗ s) · s' = p ⊗ (s * s')`. This is the convention of
algebraic `K`-theory, whose finitely generated projective modules are right modules.

The same module is obtained from the left-module extension `TauCeti.BalancedExtension` along
`fᵐᵒᵖ : Rᵐᵒᵖ →+* Sᵐᵒᵖ`, by `sᵐᵒᵖ ⊗ p ↦ p ⊗ s` (`TauCeti.RightBalancedExtension.opEquiv`). The
order of the factors matters: in `S ⊗_R P` the balancing reads `(s * f r) ⊗ p = s ⊗ (r • p)`,
while here the scalar `f r` is multiplied into `S` from the left.

The extension of scalars along a composite is the iterated extension
(`TauCeti.RightBalancedExtension.cancelBaseChange`), and extension along the identity is the
identity (`TauCeti.RightBalancedExtension.rid`). These identifications satisfy the pentagon and
both triangle identities.
The extension of the zero module is zero by the `Subsingleton` instances of
`TauCeti.BalancedTensorProduct`, since `TauCeti.RightBalancedExtension` is an `abbrev`.

## Main definitions

* `TauCeti.RightBalancedExtension.Scalars f`: the ring `S` as an `(R, S)`-bimodule, with `R`
  acting on the left through `f`.
* `TauCeti.RightBalancedExtension f P`: the right `S`-module `P ⊗_R S`, with pure tensors
  `TauCeti.RightBalancedExtension.tmul f p s`.
* `TauCeti.RightBalancedExtension.includeLeft`: the `fᵐᵒᵖ`-semilinear map `p ↦ p ⊗ 1`.
* `TauCeti.RightBalancedExtension.lift` and `TauCeti.RightBalancedExtension.liftEquiv`: the
  universal property. Right `S`-linear maps `P ⊗_R S → Q` correspond to additive maps `P → Q`
  that are right `R`-linear for the action on `Q` restricted along `f`.
* `TauCeti.RightBalancedExtension.map` and `TauCeti.RightBalancedExtension.congr`: functoriality
  in right `R`-linear maps and equivalences.
* `TauCeti.RightBalancedExtension.opEquiv`: the identification with the left-module extension
  along `fᵐᵒᵖ`, `sᵐᵒᵖ ⊗ p ↦ p ⊗ s`.
* `TauCeti.RightBalancedExtension.rid`: extension along the identity, `P ⊗_R R ≃ P`,
  `p ⊗ r ↦ p · r`.
* `TauCeti.RightBalancedExtension.cancelBaseChange`: extension along a composite,
  `(P ⊗_R S) ⊗_S T ≃ P ⊗_R T`, `(p ⊗ s) ⊗ t ↦ p ⊗ (g s * t)`.
* `TauCeti.RightBalancedExtension.lid`: extension of the regular module, `R ⊗_R S ≃ S`.
* `TauCeti.RightBalancedExtension.piScalarLeft`: extension of a finite free module,
  `Rⁿ ⊗_R S ≃ Sⁿ`. It carries the base change of a matrix acting on column vectors to the
  matrix with `f` applied to its entries
  (`TauCeti.RightBalancedExtension.piScalarLeft_map_mulVecBilin`).

## Main results

* `TauCeti.RightBalancedExtension.tmul_smul`, `TauCeti.RightBalancedExtension.smul_tmul`: the
  balancing relation and the right action of `S`.
* `TauCeti.RightBalancedExtension.cancelBaseChange_pentagon`: the two identifications
  `((P ⊗_R S) ⊗_S T) ⊗_T U ≃ P ⊗_R U` agree.
* `TauCeti.RightBalancedExtension.congr_rid_eq_cancelBaseChange` and
  `TauCeti.RightBalancedExtension.rid_eq_cancelBaseChange`: the two triangle identities.
* Extension of scalars sends finitely generated, respectively projective, right `R`-modules to
  finitely generated, respectively projective, right `S`-modules (instances).

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter II, §2.8, p. 13.
-/

public section

namespace TauCeti

open MulOpposite

universe u₁ u₂ u₃ u₄ v w

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} {U : Type u₄} [Ring R] [Ring S] [Ring T]
  [Ring U]

namespace RightBalancedExtension

/-- The ring `S` regarded as an `(R, S)`-bimodule through a ring homomorphism `f : R →+* S`:
`R` acts on the left by `r · s = f r * s` and `S` acts on the right by multiplication. This is a
type synonym so that the left `R`-action is not an instance on `S` itself. -/
@[expose]
def Scalars (_f : R →+* S) : Type u₂ := S

variable (f : R →+* S)

namespace Scalars

instance : AddCommGroup (Scalars f) := inferInstanceAs (AddCommGroup S)

/-- The left action of `R` on `S` through `f`. -/
instance : Module R (Scalars f) := Module.compHom S f

/-- The right action of `S` on itself by multiplication, as a left action of `Sᵐᵒᵖ`. -/
instance : Module Sᵐᵒᵖ (Scalars f) := inferInstanceAs (Module Sᵐᵒᵖ S)

/-- The identification of `S` with `Scalars f` as an additive group. -/
def of : S ≃+ Scalars f := AddEquiv.refl S

/-- `R` acts on `Scalars f` on the left through `f`. -/
@[simp]
theorem smul_of (r : R) (x : S) : r • of f x = of f (f r * x) := (rfl)

/-- `S` acts on `Scalars f` on the right by multiplication. -/
@[simp]
theorem op_smul_of (s : Sᵐᵒᵖ) (x : S) : s • of f x = of f (x * s.unop) := (rfl)

instance : SMulCommClass R Sᵐᵒᵖ (Scalars f) where
  smul_comm r s x := by
    obtain ⟨x, rfl⟩ := (of f).surjective x
    simp only [smul_of, op_smul_of, mul_assoc]

end Scalars

end RightBalancedExtension

/-- The extension of scalars `P ⊗_R S` of a right `R`-module `P`, encoded as a left
`Rᵐᵒᵖ`-module, along a ring homomorphism `f : R →+* S`: the balanced tensor product of `P` with
`S`, a left `R`-module through `f`. It is a right `S`-module, that is a left `Sᵐᵒᵖ`-module,
through the second factor. -/
abbrev RightBalancedExtension (f : R →+* S) (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P] :
    Type (max v u₂) :=
  BalancedTensorProduct ℤ R P (RightBalancedExtension.Scalars f)

namespace RightBalancedExtension

variable (f : R →+* S) (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- The right `S`-module structure of `P ⊗_R S`, by multiplication on the second factor. -/
instance : Module Sᵐᵒᵖ (RightBalancedExtension f P) :=
  BalancedTensorProduct.rightModule (k := ℤ) (A := R) (M := P) (N := Scalars f) Sᵐᵒᵖ

variable {P}

/-- The pure tensor `p ⊗ s` in `P ⊗_R S`. -/
def tmul (p : P) (s : S) : RightBalancedExtension f P :=
  BalancedTensorProduct.tmul ℤ R p (Scalars.of f s)

theorem tmul_def (p : P) (s : S) :
    tmul f p s = BalancedTensorProduct.tmul ℤ R p (Scalars.of f s) := (rfl)

variable {f}

@[simp]
theorem zero_tmul (s : S) : tmul f (0 : P) s = 0 :=
  BalancedTensorProduct.zero_tmul ℤ R (Scalars.of f s)

@[simp]
theorem tmul_zero (p : P) : tmul f p 0 = 0 := by
  rw [tmul_def, map_zero, BalancedTensorProduct.tmul_zero]

theorem add_tmul (p p' : P) (s : S) : tmul f (p + p') s = tmul f p s + tmul f p' s :=
  BalancedTensorProduct.add_tmul ℤ R p p' (Scalars.of f s)

theorem tmul_add (p : P) (s s' : S) : tmul f p (s + s') = tmul f p s + tmul f p s' := by
  rw [tmul_def, _root_.map_add, BalancedTensorProduct.tmul_add, tmul_def, tmul_def]

/-- The balancing relation `(p · r) ⊗ s = p ⊗ (f r * s)`. -/
theorem tmul_smul (r : Rᵐᵒᵖ) (p : P) (s : S) : tmul f (r • p) s = tmul f p (f r.unop * s) := by
  rw [tmul_def, tmul_def, ← op_unop r, BalancedTensorProduct.balance, Scalars.smul_of, unop_op]

/-- `S` acts on `P ⊗_R S` by right multiplication on the second factor:
`(p ⊗ s) · s' = p ⊗ (s * s')`. -/
@[simp]
theorem smul_tmul (s' : Sᵐᵒᵖ) (p : P) (s : S) : s' • tmul f p s = tmul f p (s * s'.unop) :=
  (BalancedTensorProduct.smul_tmul_right (k := ℤ) (A := R) (M := P) Sᵐᵒᵖ s' p _).trans
    (congrArg (BalancedTensorProduct.tmul ℤ R p) (Scalars.op_smul_of f s' s))

theorem tmul_eq_smul_tmul_one (p : P) (s : S) : tmul f p s = op s • tmul f p 1 := by
  rw [smul_tmul, unop_op, one_mul]

/-- Induction on `P ⊗_R S` by pure tensors and addition. -/
@[elab_as_elim]
theorem induction_on {C : RightBalancedExtension f P → Prop} (x : RightBalancedExtension f P)
    (tmul : ∀ p s, C (RightBalancedExtension.tmul f p s))
    (add : ∀ x y, C x → C y → C (x + y)) : C x :=
  BalancedTensorProduct.induction_on ℤ R x (fun p s ↦ tmul p ((Scalars.of f).symm s)) add

variable {Q : Type w} [AddCommGroup Q] [Module Sᵐᵒᵖ Q]

/-- Right `S`-linear maps out of `P ⊗_R S` agree once they agree on the tensors `p ⊗ 1`. -/
@[ext high]
theorem hom_ext {φ ψ : RightBalancedExtension f P →ₗ[Sᵐᵒᵖ] Q}
    (h : ∀ p, φ (tmul f p 1) = ψ (tmul f p 1)) : φ = ψ := by
  ext x
  induction x using induction_on with
  | tmul p s => rw [tmul_eq_smul_tmul_one, map_smul, map_smul, h]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]

variable (f P) in
/-- The `fᵐᵒᵖ`-semilinear map `p ↦ p ⊗ 1` into the extension of scalars. -/
def includeLeft : P →ₛₗ[RingHom.op f] RightBalancedExtension f P where
  toFun p := tmul f p 1
  map_add' p p' := add_tmul p p' 1
  map_smul' r p := by simp [tmul_smul]

@[simp]
theorem includeLeft_apply (p : P) : includeLeft f P p = tmul f p 1 := (rfl)

/-- The balanced biadditive map `(p, s) ↦ g p · s` attached to an `fᵐᵒᵖ`-semilinear map `g`. -/
private def liftAux (g : P →ₛₗ[RingHom.op f] Q) : P →ₗ[ℤ] Scalars f →ₗ[ℤ] Q :=
  LinearMap.mk₂ ℤ (fun p s ↦ op ((Scalars.of f).symm s) • g p)
    (fun _ _ _ ↦ by rw [_root_.map_add, smul_add]) (fun _ _ _ ↦ by rw [map_zsmul, smul_comm])
    (fun _ _ _ ↦ by rw [_root_.map_add, op_add, add_smul])
    (fun _ _ _ ↦ by rw [map_zsmul, MulOpposite.op_smul, smul_assoc])

private theorem liftAux_apply (g : P →ₛₗ[RingHom.op f] Q) (p : P) (s : S) :
    liftAux g p (Scalars.of f s) = op s • g p := (rfl)

private theorem liftAux_balanced (g : P →ₛₗ[RingHom.op f] Q) (r : R) (p : P) (s : Scalars f) :
    liftAux g (op r • p) s = liftAux g p (r • s) := by
  obtain ⟨s, rfl⟩ := (Scalars.of f).surjective s
  rw [Scalars.smul_of, liftAux_apply, liftAux_apply, map_smulₛₗ, RingHom.op_apply_apply, unop_op,
    smul_smul, op_mul]

/-- The right `S`-linear map `P ⊗_R S → Q`, `p ⊗ s ↦ g p · s`, induced by an
`fᵐᵒᵖ`-semilinear map `g : P → Q`. -/
def lift (g : P →ₛₗ[RingHom.op f] Q) : RightBalancedExtension f P →ₗ[Sᵐᵒᵖ] Q where
  toFun := BalancedTensorProduct.lift (liftAux g) (liftAux_balanced g)
  map_add' := _root_.map_add _
  map_smul' s x := by
    induction x using induction_on with
    | tmul p s' =>
      rw [smul_tmul]
      simp only [tmul_def, BalancedTensorProduct.lift_tmul, liftAux_apply, RingHom.id_apply,
        op_mul, op_unop, mul_smul]
    | add x y hx hy => rw [smul_add, _root_.map_add, _root_.map_add, hx, hy, smul_add]

@[simp]
theorem lift_tmul (g : P →ₛₗ[RingHom.op f] Q) (p : P) (s : S) :
    lift g (tmul f p s) = op s • g p :=
  (BalancedTensorProduct.lift_tmul (liftAux g) (liftAux_balanced g) p _).trans
    (liftAux_apply g p s)

@[simp]
theorem lift_comp_includeLeft (g : P →ₛₗ[RingHom.op f] Q) :
    (lift g).comp (includeLeft f P) = g := by
  ext p
  simp

/-- **The universal property of extension of scalars of right modules.** Right `S`-linear maps
`P ⊗_R S → Q` correspond to `fᵐᵒᵖ`-semilinear maps `P → Q`, by restriction along `p ↦ p ⊗ 1`. -/
def liftEquiv : (P →ₛₗ[RingHom.op f] Q) ≃ (RightBalancedExtension f P →ₗ[Sᵐᵒᵖ] Q) where
  toFun := lift
  invFun φ := φ.comp (includeLeft f P)
  left_inv := lift_comp_includeLeft
  right_inv φ := hom_ext fun p ↦ by simp

@[simp]
theorem liftEquiv_apply (g : P →ₛₗ[RingHom.op f] Q) : liftEquiv g = lift g := (rfl)

@[simp]
theorem liftEquiv_symm_apply (φ : RightBalancedExtension f P →ₗ[Sᵐᵒᵖ] Q) :
    liftEquiv.symm φ = φ.comp (includeLeft f P) := (rfl)

section Map

variable {P' P'' : Type*} [AddCommGroup P'] [Module Rᵐᵒᵖ P'] [AddCommGroup P'']
  [Module Rᵐᵒᵖ P'']

variable (f) in
/-- The right `S`-linear map `P ⊗_R S → P' ⊗_R S`, `p ⊗ s ↦ g p ⊗ s`, induced by a right
`R`-linear map. -/
def map (g : P →ₗ[Rᵐᵒᵖ] P') : RightBalancedExtension f P →ₗ[Sᵐᵒᵖ] RightBalancedExtension f P' :=
  lift ((includeLeft f P').comp g)

@[simp]
theorem map_tmul (g : P →ₗ[Rᵐᵒᵖ] P') (p : P) (s : S) : map f g (tmul f p s) = tmul f (g p) s := by
  rw [map, lift_tmul, LinearMap.comp_apply, includeLeft_apply, smul_tmul, unop_op, one_mul]

@[simp]
theorem map_id : map f (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) = LinearMap.id :=
  hom_ext fun p ↦ by simp

theorem map_comp (g : P →ₗ[Rᵐᵒᵖ] P') (g' : P' →ₗ[Rᵐᵒᵖ] P'') :
    map f (g'.comp g) = (map f g').comp (map f g) :=
  hom_ext fun p ↦ by simp

theorem map_add (g g' : P →ₗ[Rᵐᵒᵖ] P') : map f (g + g') = map f g + map f g' :=
  hom_ext fun p ↦ by simp [add_tmul]

variable (f) in
/-- The right `S`-linear equivalence `P ⊗_R S ≃ P' ⊗_R S`, `p ⊗ s ↦ θ p ⊗ s`, induced by a right
`R`-linear equivalence `θ`. -/
def congr (θ : P ≃ₗ[Rᵐᵒᵖ] P') : RightBalancedExtension f P ≃ₗ[Sᵐᵒᵖ] RightBalancedExtension f P' :=
  LinearEquiv.ofLinearMap (map f θ.toLinearMap) (map f θ.symm.toLinearMap)
    (hom_ext fun p ↦ by simp) (hom_ext fun p ↦ by simp)

@[simp]
theorem congr_tmul (θ : P ≃ₗ[Rᵐᵒᵖ] P') (p : P) (s : S) :
    congr f θ (tmul f p s) = tmul f (θ p) s :=
  map_tmul _ p s

@[simp]
theorem congr_symm (θ : P ≃ₗ[Rᵐᵒᵖ] P') : (congr f θ).symm = congr f θ.symm := (rfl)

/-- Transport of `P ⊗_R S` along an equality of ring homomorphisms. -/
def congrRingHom {f' : R →+* S} (h : f = f') :
    RightBalancedExtension f P ≃ₗ[Sᵐᵒᵖ] RightBalancedExtension f' P := by
  subst f'
  exact .refl _ _

/-- Transport along an equality of ring homomorphisms keeps both factors of a pure tensor. -/
@[simp]
theorem congrRingHom_tmul {f' : R →+* S} (h : f = f') (p : P) (s : S) :
    congrRingHom h (tmul f p s) = tmul f' p s := by
  subst f'
  rfl

/-- Transport along reflexive equality is the identity equivalence. -/
@[simp]
theorem congrRingHom_refl : congrRingHom (P := P) (rfl : f = f) = LinearEquiv.refl Sᵐᵒᵖ _ := (rfl)

/-- The inverse of transport along `h` is transport along `h.symm`. -/
@[simp]
theorem congrRingHom_symm {f' : R →+* S} (h : f = f') :
    (congrRingHom h).symm = congrRingHom (P := P) h.symm := by
  subst f'
  rfl

/-- Successive transports compose to transport along the transitive equality. -/
@[simp]
theorem congrRingHom_trans {f' f'' : R →+* S} (h : f = f') (h' : f' = f'') :
    (congrRingHom (P := P) h).trans (congrRingHom h') = congrRingHom (h.trans h') := by
  subst f' f''
  rfl

end Map

section Opposite

variable (f P)

/-- **Right-module extension as left-module extension over opposite rings.** The extension
`Sᵐᵒᵖ ⊗_{Rᵐᵒᵖ} P` of the left `Rᵐᵒᵖ`-module `P` along `fᵐᵒᵖ` is `P ⊗_R S`, by
`sᵐᵒᵖ ⊗ p ↦ p ⊗ s`. -/
def opEquiv : BalancedExtension (RingHom.op f) P ≃ₗ[Sᵐᵒᵖ] RightBalancedExtension f P :=
  LinearEquiv.ofLinearMap (BalancedExtension.lift (includeLeft f P))
    (lift (BalancedExtension.includeRight (RingHom.op f) P))
    (hom_ext fun p ↦ by simp) (BalancedExtension.hom_ext fun p ↦ by simp)

variable {f P}

@[simp]
theorem opEquiv_tmul (s : Sᵐᵒᵖ) (p : P) :
    opEquiv f P (BalancedExtension.tmul (RingHom.op f) s p) = tmul f p s.unop := by
  simp [opEquiv]

@[simp]
theorem opEquiv_symm_tmul (p : P) (s : S) :
    (opEquiv f P).symm (tmul f p s) = BalancedExtension.tmul (RingHom.op f) (op s) p := by
  simp [opEquiv, BalancedExtension.smul_tmul]

/-- `opEquiv` is natural in the right `R`-module. -/
theorem opEquiv_symm_map {P' : Type*} [AddCommGroup P'] [Module Rᵐᵒᵖ P'] (g : P →ₗ[Rᵐᵒᵖ] P')
    (x : RightBalancedExtension f P) :
    (opEquiv f P').symm (map f g x) =
      BalancedExtension.map (RingHom.op f) g ((opEquiv f P).symm x) :=
  congr($(hom_ext (φ := (opEquiv f P').symm.toLinearMap ∘ₗ map f g)
    (ψ := BalancedExtension.map (RingHom.op f) g ∘ₗ (opEquiv f P).symm.toLinearMap)
    fun p ↦ by simp) x)

/-- Extension of scalars preserves finite generation. -/
instance [Module.Finite Rᵐᵒᵖ P] : Module.Finite Sᵐᵒᵖ (RightBalancedExtension f P) :=
  Module.Finite.equiv (opEquiv f P)

/-- Extension of scalars preserves projectivity. -/
instance [Module.Projective Rᵐᵒᵖ P] : Module.Projective Sᵐᵒᵖ (RightBalancedExtension f P) :=
  Module.Projective.of_equiv (opEquiv f P)

end Opposite

section Identity

variable (R P) in
/-- The identity of `P`, as a semilinear map over `RingHom.op (RingHom.id R)`. -/
private def ridAux : P →ₛₗ[RingHom.op (RingHom.id R)] P where
  toFun p := p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ridAux_apply (p : P) : ridAux R P p = p := (rfl)

variable (R P) in
/-- **Extension along the identity.** `P ⊗_R R ≃ P`, `p ⊗ r ↦ p · r`. -/
def rid : RightBalancedExtension (RingHom.id R) P ≃ₗ[Rᵐᵒᵖ] P :=
  LinearEquiv.ofLinearMap
    (lift (ridAux R P))
    { toFun := fun p ↦ tmul (RingHom.id R) p 1
      map_add' := fun p p' ↦ add_tmul p p' 1
      map_smul' := fun r p ↦ by simp [tmul_smul] }
    (LinearMap.ext fun p ↦ by simp [ridAux_apply]) (hom_ext fun p ↦ by simp [ridAux_apply])

@[simp]
theorem rid_tmul (p : P) (r : R) : rid R P (tmul (RingHom.id R) p r) = op r • p := by
  simp [rid, ridAux_apply]

@[simp]
theorem rid_symm_apply (p : P) : (rid R P).symm p = tmul (RingHom.id R) p 1 := (rfl)

end Identity

section Composition

variable (f) (g : S →+* T)

/-- The map `Scalars f → Scalars (g.comp f)` given by `g`, which is `R`-equivariant. -/
private def scalarsMap : Scalars f →ₗ[ℤ] Scalars (g.comp f) :=
  (((Scalars.of (g.comp f)).toAddMonoidHom.comp (g : S →+ T)).comp
    (Scalars.of f).symm.toAddMonoidHom).toIntLinearMap

private theorem scalarsMap_of (s : S) :
    scalarsMap f g (Scalars.of f s) = Scalars.of (g.comp f) (g s) := (rfl)

private theorem scalarsMap_smul (r : R) (x : Scalars f) :
    scalarsMap f g (r • x) = r • scalarsMap f g x := by
  obtain ⟨s, rfl⟩ := (Scalars.of f).surjective x
  rw [Scalars.smul_of, scalarsMap_of, scalarsMap_of, Scalars.smul_of, map_mul, RingHom.comp_apply]

/-- The additive map `P ⊗_R S → P ⊗_R T`, `p ⊗ s ↦ p ⊗ g s`. -/
private def changeScalarsAux :
    RightBalancedExtension f P →ₗ[ℤ] RightBalancedExtension (g.comp f) P :=
  BalancedTensorProduct.map LinearMap.id (scalarsMap f g) (fun _ _ ↦ rfl) (scalarsMap_smul f g)

private theorem changeScalarsAux_tmul (p : P) (s : S) :
    changeScalarsAux f g (tmul f p s) = tmul (g.comp f) p (g s) :=
  BalancedTensorProduct.map_tmul _ _ _ _ _ _

/-- The `gᵐᵒᵖ`-semilinear map `P ⊗_R S → P ⊗_R T`, `p ⊗ s ↦ p ⊗ g s`, underlying
`cancelBaseChange`. -/
private def changeScalars :
    RightBalancedExtension f P →ₛₗ[RingHom.op g] RightBalancedExtension (g.comp f) P where
  toFun := changeScalarsAux f g
  map_add' := _root_.map_add _
  map_smul' s x := by
    induction x using induction_on with
    | tmul p s' =>
      rw [smul_tmul, changeScalarsAux_tmul, changeScalarsAux_tmul, RingHom.op_apply_apply,
        smul_tmul, unop_op, map_mul]
    | add x y hx hy => simp only [smul_add, _root_.map_add, hx, hy]

private theorem changeScalars_tmul (p : P) (s : S) :
    changeScalars f g (tmul f p s) = tmul (g.comp f) p (g s) :=
  changeScalarsAux_tmul f g p s

/-- **Extension along a composite.** For ring homomorphisms `f : R →+* S` and `g : S →+* T`,
`(P ⊗_R S) ⊗_S T ≃ P ⊗_R T`, `(p ⊗ s) ⊗ t ↦ p ⊗ (g s * t)`. -/
def cancelBaseChange :
    RightBalancedExtension g (RightBalancedExtension f P) ≃ₗ[Tᵐᵒᵖ]
      RightBalancedExtension (g.comp f) P :=
  haveI : RingHomCompTriple (RingHom.op f) (RingHom.op g) (RingHom.op (g.comp f)) :=
    ⟨RingHom.ext fun _ ↦ rfl⟩
  LinearEquiv.ofLinearMap (lift (changeScalars f g))
    (lift ((includeLeft g _).comp (includeLeft f P)))
    (hom_ext fun p ↦ by simp [changeScalars_tmul])
    (hom_ext fun x ↦ by
      induction x using induction_on with
      | tmul p s =>
        simp only [LinearMap.comp_apply, lift_tmul, changeScalars_tmul, one_mul,
          includeLeft_apply, smul_tmul, unop_op, LinearMap.id_apply]
        rw [tmul_eq_smul_tmul_one (f := f) p s, tmul_smul, unop_op]
      | add x y hx hy => simp only [add_tmul, _root_.map_add, hx, hy])

@[simp]
theorem cancelBaseChange_tmul (p : P) (s : S) (t : T) :
    cancelBaseChange f g (tmul g (tmul f p s) t) = tmul (g.comp f) p (g s * t) := by
  simp [cancelBaseChange, changeScalars_tmul]

@[simp]
theorem cancelBaseChange_symm_tmul (p : P) (t : T) :
    (cancelBaseChange f g).symm (tmul (g.comp f) p t) = tmul g (tmul f p 1) t := by
  rw [LinearEquiv.symm_apply_eq, cancelBaseChange_tmul, map_one, one_mul]

/-- **The pentagon identity.** For ring homomorphisms `f : R →+* S`, `g : S →+* T` and
`h : T →+* U`, the two identifications `((P ⊗_R S) ⊗_S T) ⊗_T U ≃ P ⊗_R U` built from
`cancelBaseChange` agree. Their targets agree because `(h.comp g).comp f` is
`h.comp (g.comp f)` by definition (`RingHom.comp_assoc` holds by `rfl`). -/
theorem cancelBaseChange_pentagon (h : T →+* U) :
    (congr h (cancelBaseChange (P := P) f g)).trans (cancelBaseChange (g.comp f) h) =
      (cancelBaseChange (P := RightBalancedExtension f P) g h).trans
        (cancelBaseChange f (h.comp g)) := by
  refine LinearEquiv.toLinearMap_injective (hom_ext fun x ↦ ?_)
  induction x using induction_on with
  | tmul y t =>
    induction y using induction_on with
    | tmul p s =>
      -- Both sides are `p ⊗ (h (g s) * h t)`, over the definitionally equal ring homomorphisms
      -- `h.comp (g.comp f)` and `(h.comp g).comp f`.
      simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, congr_tmul, cancelBaseChange_tmul,
        RingHom.comp_apply, map_mul, mul_one]
      rfl
    | add y y' hy hy' => simpa only [add_tmul, _root_.map_add] using congrArg₂ (· + ·) hy hy'
  | add x x' hx hx' => simpa only [add_tmul, _root_.map_add] using congrArg₂ (· + ·) hx hx'

/-- **The left triangle identity.** Extending `P ⊗_R R ≃ P` along `f` is the identification
`(P ⊗_R R) ⊗_R S ≃ P ⊗_R S` of `cancelBaseChange`, up to `f ∘ id = f`. -/
theorem congr_rid_eq_cancelBaseChange :
    congr f (rid R P) = (cancelBaseChange (RingHom.id R) f).trans (congrRingHom f.comp_id) := by
  refine LinearEquiv.toLinearMap_injective (hom_ext fun x ↦ ?_)
  induction x using induction_on with
  | tmul p r =>
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, cancelBaseChange_tmul,
      congrRingHom_tmul, congr_tmul, rid_tmul, tmul_smul, unop_op]
  | add x x' hx hx' => simpa only [add_tmul, _root_.map_add] using congrArg₂ (· + ·) hx hx'

/-- **The right triangle identity.** The identification `(P ⊗_R S) ⊗_S S ≃ P ⊗_R S` of
`cancelBaseChange` along the identity of `S` is `rid` of the right `S`-module `P ⊗_R S`, up to
`id ∘ f = f`. -/
theorem rid_eq_cancelBaseChange :
    rid S (RightBalancedExtension f P) =
      (cancelBaseChange f (RingHom.id S)).trans (congrRingHom f.id_comp) := by
  refine LinearEquiv.toLinearMap_injective (hom_ext fun x ↦ ?_)
  induction x using induction_on with
  | tmul p s =>
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, cancelBaseChange_tmul,
      congrRingHom_tmul, rid_tmul, smul_tmul, unop_op, RingHom.id_apply]
  | add x x' hx hx' => simpa only [add_tmul, _root_.map_add] using congrArg₂ (· + ·) hx hx'

end Composition

section RegularModule

variable (f)

/-- **Extension of the regular module.** `R ⊗_R S ≃ S`, sending `r ⊗ s` to `f r * s`. It is
`TauCeti.BalancedTensorProduct.lid` for the left `R`-module `Scalars f`, which preserves the right
action of `S` by `TauCeti.BalancedTensorProduct.lid_smul_right`. -/
noncomputable def lid : RightBalancedExtension f R ≃ₗ[Sᵐᵒᵖ] S where
  __ := (BalancedTensorProduct.lid ℤ R (Scalars f)).toAddEquiv.trans (Scalars.of f).symm
  map_smul' s x := BalancedTensorProduct.lid_smul_right ℤ R (Scalars f) Sᵐᵒᵖ s x

@[simp]
theorem lid_tmul (r : R) (s : S) : lid f (tmul f r s) = f r * s :=
  BalancedTensorProduct.lid_tmul ℤ R (Scalars f) r (Scalars.of f s)

@[simp]
theorem lid_symm_apply (s : S) : (lid f).symm s = tmul f 1 s :=
  BalancedTensorProduct.lid_symm_apply ℤ R (Scalars f) (Scalars.of f s)

end RegularModule

section Pi

variable (f) (ι : Type*) [Fintype ι]

/-- The `fᵐᵒᵖ`-semilinear map `(ι → R) → (ι → S)` applying `f` to every coordinate. -/
private def piMap : (ι → R) →ₛₗ[RingHom.op f] (ι → S) where
  toFun x i := f (x i)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

/-- **Extension of a finite free module.** `Rⁿ ⊗_R S ≃ Sⁿ`, sending `x ⊗ s` to
`i ↦ f (x i) * s`. Its inverse sends `v` to `∑ i, eᵢ ⊗ v i` (`piScalarLeft_symm_apply`). -/
noncomputable def piScalarLeft : RightBalancedExtension f (ι → R) ≃ₗ[Sᵐᵒᵖ] (ι → S) := by
  classical
  exact LinearEquiv.ofLinearMap (lift (piMap f ι))
    { toFun := fun v ↦ ∑ i, tmul f (Pi.single i 1) (v i)
      map_add' := fun v w ↦ by simp [tmul_add, Finset.sum_add_distrib]
      map_smul' := fun s v ↦ by simp [Finset.smul_sum] }
    (by
      ext v j
      simp [piMap, Pi.single_apply])
    (hom_ext fun x ↦ by
      -- `eᵢ ⊗ f (x i) = (eᵢ · x i) ⊗ 1`, and the vectors `eᵢ · x i` sum to `x`.
      have key (i : ι) :
          tmul f (Pi.single i (1 : R)) (f (x i)) = includeLeft f _ (Pi.single i (x i) : ι → R) := by
        have hv : op (x i) • Pi.single i (1 : R) = (Pi.single i (x i) : ι → R) := by
          ext j
          rcases eq_or_ne j i with rfl | hj <;> simp [*]
        rw [includeLeft_apply, ← hv, tmul_smul, unop_op, mul_one]
      simp only [piMap, key, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, lift_tmul, op_one, one_smul, LinearMap.id_apply]
      conv_rhs => rw [← Finset.univ_sum_single x]
      rw [← includeLeft_apply, map_sum])

variable {f ι}

@[simp]
theorem piScalarLeft_tmul (x : ι → R) (s : S) :
    piScalarLeft f ι (tmul f x s) = fun i ↦ f (x i) * s := by
  ext i
  simp [piScalarLeft, piMap]

@[simp]
theorem piScalarLeft_symm_apply [DecidableEq ι] (v : ι → S) :
    (piScalarLeft f ι).symm v = ∑ i, tmul f (Pi.single i 1) (v i) := by
  rw [LinearEquiv.symm_apply_eq, map_sum]
  ext j
  simp [Pi.single_apply]

open Matrix in
/-- **Base change of a matrix acting on column vectors.** Through `piScalarLeft`, the extension of
scalars of the right `R`-linear map `x ↦ u *ᵥ x` is `v ↦ f(u) *ᵥ v`, where `f(u)` is `u` with `f`
applied to every entry. -/
theorem piScalarLeft_map_mulVecBilin {κ : Type*} [Fintype κ] (u : Matrix κ ι R)
    (x : RightBalancedExtension f (ι → R)) :
    piScalarLeft f κ (map f (Matrix.mulVecBilin R Rᵐᵒᵖ u) x) =
      u.map f *ᵥ piScalarLeft f ι x := by
  induction x using induction_on with
  | tmul x s =>
    ext k
    simp [mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy, _root_.map_add, mulVec_add]

end Pi

end RightBalancedExtension

end TauCeti
