/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Along
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
public import TauCeti.Topology.Algebra.Ring.Frobenius

/-!
# Coefficient twists of continuous representations

For a continuous ring homomorphism `f : A →+* B`, the *extension of scalars along `f`* of a
continuous representation `ρ` of `Γ` on a finite `A`-module `M` is the continuous representation
`ρ.baseChangeAlong f` on `B ⊗[A, f] M`: Tau Ceti's `ContinuousRep.baseChange` for the `A`-algebra
structure `f.toAlgebra` on `B`. For a continuous ring automorphism `σ` of `A` this is the
*coefficient twist* `ρ.coeffTwist σ = ρ^σ`: the representation whose matrices, in the base-changed
basis, are those of `ρ` with `σ` applied entrywise. For a perfect ring `A` of characteristic `p`,
such as a finite field or `AlgebraicClosure (ZMod p)`, the *Frobenius twist*
`ρ.frobTwist p = ρ^{(p)}` is the coefficient twist by `frobeniusEquiv A p`. Twisting coefficients
is not conjugation in `Γ`: a character `χ` twists to `χ ^ p`.

The characteristic polynomial, determinant and trace of `ρ^σ(g)` are those of `ρ(g)` with `σ`
applied to the coefficients. Twisting by the identity gives back `ρ`, and twisting by `σ` and
then by `τ` is twisting by `σ.trans τ = τ ∘ σ`, up to isomorphism. Over `ZMod p` the Frobenius
twist is the identity.

## Implementation notes

`ContinuousRep.baseChange` takes the coefficient ring map as an `[Algebra A B]` instance. Base
change along an automorphism `σ` of `A` cannot use an instance: an instance `Algebra A A` through
`σ` would compete with `Algebra.id`, and on `A ⊗[A] M` the `A`-module structure acting on the left
factor would compete with the one acting through the base ring. The carrier is therefore the type
synonym `TauCeti.TensorAlong f M` of `B ⊗[A] M` for `f.toAlgebra`, which carries only its
`B`-module structure on the left factor and its `B`-module topology. All constructions are
`ContinuousRep.baseChange` and its isomorphisms `baseChangeSelfIso`, `baseChangeTransIso` and
`baseChangeOfCharacterIso` with `f.toAlgebra` installed locally, so the twist is literally the base
change along `σ`.

## Main definitions

* `TauCeti.ContinuousRep.baseChangeAlong`: extension of scalars of a continuous representation
  along a continuous ring homomorphism.
* `TauCeti.ContinuousRep.coeffTwist`: the coefficient twist `ρ^σ` by a continuous ring
  automorphism.
* `TauCeti.ContinuousRep.frobTwist`: the Frobenius twist `ρ^{(p)}`.
* `TauCeti.ContinuousRep.coeffTwistReflIso` and `TauCeti.ContinuousRep.coeffTwistTransIso`: the
  twist by the identity, and composition of twists.
* `TauCeti.ContinuousRep.coeffTwistOfCharacterIso`: the twist of a character line is the line of
  the twisted character.

## Main statements

* `TauCeti.ContinuousRep.toMatrix_coeffTwist_apply`: the entrywise formula.
* `TauCeti.ContinuousRep.charpoly_coeffTwist_apply`, `TauCeti.ContinuousRep.det_coeffTwist_apply`
  and `TauCeti.ContinuousRep.trace_coeffTwist_apply`: characteristic polynomials, determinants and
  traces are transformed by `σ`.
* `TauCeti.ContinuousRep.not_nonempty_iso_frobTwist_ofCharacter`: a character `χ` whose values
  are not all fixed by Frobenius, for instance one valued in `F_{p²}ˣ` with an element of order
  `p² - 1` in its image, is not isomorphic to its Frobenius twist `χ ^ p`.

## References

* Newton–Thorne 2026, display (1.1), p. 3, and proof of Lemma 5.8, p. 43.
* Deligne–Serre 1974, *Formes modulaires de poids 1*, proof of Lemme 6.13, p. 523.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace ContinuousRep

-- Every construction below installs the same local structures before calling main's base change
-- API, and its evaluation lemmas typecheck only if they install exactly the same ones. This
-- tactic installs, for `f : A →+* B` continuous by `hf` and an `A`-module `X`, the algebra
-- structure `f.toAlgebra`, its `ContinuousSMul A B` instance and the `B`-module topology on
-- `B ⊗[A] X`, so that each declaration shares one copy.
local macro "along_instances " f:term:max hf:term:max A:term:max B:term:max X:term:max :
    tactic =>
  `(tactic| (
    let := RingHom.toAlgebra $f
    have : ContinuousSMul $A $B := continuousSMul_of_algebraMap $A $B $hf
    let : TopologicalSpace ($B ⊗[$A] $X) := moduleTopology $B _
    have : IsModuleTopology $B ($B ⊗[$A] $X) := ⟨rfl⟩))

-- The local structures for extending along `f : A →+* B` and then along `g : B →+* C`.
local macro "along_comp_instances " f:term:max g:term:max hf:term:max hg:term:max A:term:max
    B:term:max C:term:max M:term:max : tactic =>
  `(tactic| (
    along_instances $f $hf $A $B $M
    along_instances $g $hg $B $C ($B ⊗[$A] $M)
    along_instances (RingHom.comp $g $f) (Continuous.comp $hg $hf :) $A $C $M
    have : IsScalarTower $A $B $C := IsScalarTower.of_algebraMap_eq fun _ => rfl))

section BaseChangeAlong

variable {Γ A B M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [AddCommMonoid M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]

/-- **Extension of scalars of a continuous representation along a continuous ring
homomorphism** `f : A →+* B`: `ContinuousRep.baseChange` for the `A`-algebra structure
`f.toAlgebra` on `B`, acting on `B ⊗[A, f] M` by `b ⊗ m ↦ b ⊗ ρ(g) m`. -/
def baseChangeAlong (f : A →+* B) (hf : Continuous f) (ρ : ContinuousRep Γ A M) :
    ContinuousRep Γ B (TensorAlong f M) := by
  along_instances f hf A B M
  exact ρ.baseChange B

variable (f : A →+* B) (hf : Continuous f) (ρ : ContinuousRep Γ A M)

/-- The operators of the extension of scalars along `f` are the base changes of the operators
of `ρ`. -/
theorem baseChangeAlong_apply (g : Γ) :
    ρ.baseChangeAlong f hf g =
      letI := f.toAlgebra
      ((ρ g).baseChange B : TensorAlong f M →ₗ[B] TensorAlong f M) := by
  along_instances f hf A B M
  exact ρ.baseChange_apply B g

/-- The extension of scalars along `f` acts on pure tensors by `b ⊗ m ↦ b ⊗ ρ(g) m`. -/
@[simp]
theorem baseChangeAlong_apply_tmul (g : Γ) (b : B) (m : M) :
    ρ.baseChangeAlong f hf g (TensorAlong.tmul b m) = TensorAlong.tmul b (ρ g m) := by
  let := f.toAlgebra
  rw [baseChangeAlong_apply, TensorAlong.tmul_def, TensorAlong.tmul_def]
  exact LinearMap.baseChange_tmul (ρ g) b m

/-- **Entrywise formula.** In the base-changed basis, the matrix of the extension of scalars of
`ρ` along `f` at `g` is the matrix of `ρ g` with `f` applied to its entries. -/
@[simp]
theorem toMatrix_baseChangeAlong_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A M) (g : Γ) :
    LinearMap.toMatrix (TensorAlong.basis f b) (TensorAlong.basis f b)
        (ρ.baseChangeAlong f hf g) =
      (LinearMap.toMatrix b b (ρ g)).map f := by
  let := f.toAlgebra
  rw [baseChangeAlong_apply, TensorAlong.basis_def]
  exact LinearMap.toMatrix_baseChange B (ρ g) b b

end BaseChangeAlong

section BaseChangeAlongCharpoly

variable {Γ A B M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [AddCommGroup M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] [Module.Free A M]
  (f : A →+* B) (hf : Continuous f) (ρ : ContinuousRep Γ A M)

/-- The characteristic polynomials of the extension of scalars along `f` are those of `ρ` with
`f` applied to the coefficients. -/
@[simp]
theorem charpoly_baseChangeAlong_apply (g : Γ) :
    (ρ.baseChangeAlong f hf g).charpoly = (ρ g).charpoly.map f := by
  let := f.toAlgebra
  rw [baseChangeAlong_apply]
  exact LinearMap.charpoly_baseChange (ρ g) B

/-- The determinants of the extension of scalars along `f` are the images of those of `ρ`. -/
@[simp]
theorem det_baseChangeAlong_apply (g : Γ) :
    LinearMap.det (ρ.baseChangeAlong f hf g) = f (LinearMap.det (ρ g)) := by
  let := f.toAlgebra
  rw [baseChangeAlong_apply]
  exact LinearMap.det_baseChange (ρ g)

/-- The traces of the extension of scalars along `f` are the images of those of `ρ`. -/
@[simp]
theorem trace_baseChangeAlong_apply (g : Γ) :
    LinearMap.trace B (TensorAlong f M) (ρ.baseChangeAlong f hf g) =
      f (LinearMap.trace A M (ρ g)) := by
  let := f.toAlgebra
  rw [baseChangeAlong_apply]
  exact LinearMap.trace_baseChange (ρ g) B

end BaseChangeAlongCharpoly

section BaseChangeAlongIso

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]

/-- **Extension of scalars in stages**: extending along `f : A →+* B` and then along
`g : B →+* C` is extending along `g ∘ f`, by `baseChangeTransIso`. -/
def baseChangeAlongCompIso [AddCommMonoid M] [Module A M] [TopologicalSpace M]
    [IsModuleTopology A M] [Module.Finite A M] (ρ : ContinuousRep Γ A M) {B C : Type*}
    [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [CommRing C] [TopologicalSpace C]
    [IsTopologicalSemiring C] (f : A →+* B) (g : B →+* C) (hf : Continuous f)
    (hg : Continuous g) :
    Iso ((ρ.baseChangeAlong f hf).baseChangeAlong g hg)
      (ρ.baseChangeAlong (g.comp f) (hg.comp hf)) := by
  along_comp_instances f g hf hg A B C M
  exact ρ.baseChangeTransIso B C

section CompIso

variable [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] (ρ : ContinuousRep Γ A M) {B C : Type*} [CommRing B] [TopologicalSpace B]
  [IsTopologicalSemiring B] [CommRing C] [TopologicalSpace C] [IsTopologicalSemiring C]
  (f : A →+* B) (g : B →+* C) (hf : Continuous f) (hg : Continuous g)

@[simp]
theorem baseChangeAlongCompIso_tmul (c : C) (b : B) (m : M) :
    ρ.baseChangeAlongCompIso f g hf hg (TensorAlong.tmul c (TensorAlong.tmul b m)) =
      TensorAlong.tmul (g b * c) m := by
  along_comp_instances f g hf hg A B C M
  rw [TensorAlong.tmul_def, TensorAlong.tmul_def, TensorAlong.tmul_def]
  exact ρ.baseChangeTransIso_tmul B C c b m

@[simp]
theorem baseChangeAlongCompIso_symm_tmul (c : C) (m : M) :
    (ρ.baseChangeAlongCompIso f g hf hg).symm (TensorAlong.tmul c m) =
      TensorAlong.tmul c (TensorAlong.tmul 1 m) := by
  along_comp_instances f g hf hg A B C M
  rw [TensorAlong.tmul_def, TensorAlong.tmul_def, TensorAlong.tmul_def]
  exact ρ.baseChangeTransIso_symm_tmul B C c m

end CompIso

section OfCharacter

variable [IsTopologicalSemiring A] {B : Type*} [CommRing B] [TopologicalSpace B]
  [IsTopologicalSemiring B] (f : A →+* B) (hf : Continuous f) (χ : Γ →ₜ* Aˣ)

/-- **Extension of scalars of a character line along `f` is the line of the extended
character** `f ∘ χ`, by `baseChangeOfCharacterIso`. -/
def baseChangeAlongOfCharacterIso :
    Iso ((ofCharacter χ).baseChangeAlong f hf)
      (ofCharacter ((ContinuousMonoidHom.unitsMap ⟨(f : A →* B), hf⟩).comp χ)) := by
  along_instances f hf A B A
  exact baseChangeOfCharacterIso B χ

@[simp]
theorem baseChangeAlongOfCharacterIso_tmul (b : B) (a : A) :
    baseChangeAlongOfCharacterIso f hf χ (TensorAlong.tmul b a) = f a * b := by
  along_instances f hf A B A
  rw [TensorAlong.tmul_def]
  exact (baseChangeOfCharacterIso_tmul B χ b a).trans (Algebra.smul_def a b)

end OfCharacter

end BaseChangeAlongIso

section IdIso

-- These declarations use main's `baseChangeSelfIso` API, stated for `Algebra.id A`, at the type
-- `TensorAlong (RingHom.id A) M`. They rely on the definitional equality
-- `(RingHom.id A).toAlgebra = Algebra.id A`: Mathlib defines `Algebra.id A` as
-- `(RingHom.id A).toAlgebra` with its scalar action replaced by multiplication, which agrees with
-- `RingHom.id A c * x` once `RingHom.id` is unfolded. So no algebra structure is installed here;
-- only the `A`-module topology on `A ⊗[A] M` is.

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M] (ρ : ContinuousRep Γ A M)

/-- **Extension of scalars along the identity is trivial**: `A ⊗[A, id] M ≅ M`, by
`baseChangeSelfIso`. -/
def baseChangeAlongIdIso : Iso (ρ.baseChangeAlong (RingHom.id A) continuous_id) ρ :=
  letI : TopologicalSpace (A ⊗[A] M) := moduleTopology A _
  haveI : IsModuleTopology A (A ⊗[A] M) := ⟨rfl⟩
  ρ.baseChangeSelfIso

@[simp]
theorem baseChangeAlongIdIso_tmul (a : A) (m : M) :
    ρ.baseChangeAlongIdIso (TensorAlong.tmul a m) = a • m := by
  let : TopologicalSpace (A ⊗[A] M) := moduleTopology A _
  have : IsModuleTopology A (A ⊗[A] M) := ⟨rfl⟩
  rw [TensorAlong.tmul_def]
  exact ρ.baseChangeSelfIso_tmul a m

@[simp]
theorem baseChangeAlongIdIso_symm_apply (m : M) :
    ρ.baseChangeAlongIdIso.symm m = TensorAlong.tmul 1 m := by
  let : TopologicalSpace (A ⊗[A] M) := moduleTopology A _
  have : IsModuleTopology A (A ⊗[A] M) := ⟨rfl⟩
  rw [TensorAlong.tmul_def]
  exact ρ.baseChangeSelfIso_symm_apply m

end IdIso

section CoeffTwist

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M]
  (σ : A ≃+* A) (hσ : Continuous σ) (ρ : ContinuousRep Γ A M)

/-- **The coefficient twist** `ρ^σ` of a continuous representation by a continuous ring
automorphism `σ` of the coefficients: the extension of scalars of `ρ` along `σ`, on
`A ⊗[A, σ] M`. In a base-changed basis its matrices are those of `ρ` with `σ` applied entrywise
(`toMatrix_coeffTwist_apply`). -/
def coeffTwist : ContinuousRep Γ A (TensorAlong (σ : A →+* A) M) :=
  ρ.baseChangeAlong (σ : A →+* A) hσ

/-- The coefficient twist by `σ` is the extension of scalars along `σ`. -/
theorem coeffTwist_eq_baseChangeAlong :
    ρ.coeffTwist σ hσ = ρ.baseChangeAlong (σ : A →+* A) hσ :=
  (rfl)

@[simp]
theorem coeffTwist_apply_tmul (g : Γ) (a : A) (m : M) :
    ρ.coeffTwist σ hσ g (TensorAlong.tmul a m) = TensorAlong.tmul a (ρ g m) :=
  ρ.baseChangeAlong_apply_tmul (σ : A →+* A) hσ g a m

/-- **Entrywise formula** for the coefficient twist: in the base-changed basis, the matrix of
`ρ^σ(g)` is the matrix of `ρ(g)` with `σ` applied to each entry. -/
@[simp]
theorem toMatrix_coeffTwist_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A M) (g : Γ) :
    LinearMap.toMatrix (TensorAlong.basis (σ : A →+* A) b) (TensorAlong.basis (σ : A →+* A) b)
        (ρ.coeffTwist σ hσ g) =
      (LinearMap.toMatrix b b (ρ g)).map σ :=
  ρ.toMatrix_baseChangeAlong_apply (σ : A →+* A) hσ b g

/-- **The twist by the identity** is `ρ` itself, up to isomorphism. -/
def coeffTwistReflIso : Iso (ρ.coeffTwist (RingEquiv.refl A) continuous_id) ρ :=
  ρ.baseChangeAlongIdIso

/-- `coeffTwistReflIso` sends `a ⊗ m` to `a • m`. Not `@[simp]`: simp rewrites the coercion of
`RingEquiv.refl A` inside the type of the argument, so the left-hand side is not in simp normal
form. -/
theorem coeffTwistReflIso_tmul (a : A) (m : M) :
    ρ.coeffTwistReflIso (TensorAlong.tmul a m) = a • m :=
  ρ.baseChangeAlongIdIso_tmul a m

/-- The inverse of `coeffTwistReflIso` sends `m` to `1 ⊗ m`. Not `@[simp]`, as for
`coeffTwistReflIso_tmul`. -/
theorem coeffTwistReflIso_symm_apply (m : M) :
    ρ.coeffTwistReflIso.symm m = TensorAlong.tmul 1 m :=
  ρ.baseChangeAlongIdIso_symm_apply m

/-- A twist by an automorphism equal to the identity is isomorphic to `ρ`. -/
def coeffTwistIsoOfEqRefl (h : σ = RingEquiv.refl A) : Iso (ρ.coeffTwist σ hσ) ρ := by
  subst h
  exact ρ.coeffTwistReflIso

/-- `coeffTwistIsoOfEqRefl` sends `a ⊗ m` to `a • m`. -/
@[simp]
theorem coeffTwistIsoOfEqRefl_tmul (h : σ = RingEquiv.refl A) (a : A) (m : M) :
    ρ.coeffTwistIsoOfEqRefl σ hσ h (TensorAlong.tmul a m) = a • m := by
  subst h
  exact ρ.coeffTwistReflIso_tmul a m

/-- **Composition of twists**: twisting by `σ` and then by `τ` is twisting by
`σ.trans τ = τ ∘ σ`. -/
def coeffTwistTransIso (τ : A ≃+* A) (hτ : Continuous τ) :
    Iso ((ρ.coeffTwist σ hσ).coeffTwist τ hτ) (ρ.coeffTwist (σ.trans τ) (hτ.comp hσ)) :=
  ρ.baseChangeAlongCompIso (σ : A →+* A) (τ : A →+* A) hσ hτ

/-- `coeffTwistTransIso` sends `c ⊗ (b ⊗ m)` to `τ b * c ⊗ m`. Not `@[simp]`: simp rewrites the
coercion of `σ.trans τ` inside the type of the image, so the left-hand side is not in simp normal
form. -/
theorem coeffTwistTransIso_tmul (τ : A ≃+* A) (hτ : Continuous τ) (c b : A) (m : M) :
    ρ.coeffTwistTransIso σ hσ τ hτ (TensorAlong.tmul c (TensorAlong.tmul b m)) =
      TensorAlong.tmul (τ b * c) m :=
  ρ.baseChangeAlongCompIso_tmul (σ : A →+* A) (τ : A →+* A) hσ hτ c b m

/-- The inverse of `coeffTwistTransIso` sends `c ⊗ m` to `c ⊗ (1 ⊗ m)`. Not `@[simp]`, as for
`coeffTwistTransIso_tmul`. -/
theorem coeffTwistTransIso_symm_tmul (τ : A ≃+* A) (hτ : Continuous τ) (c : A) (m : M) :
    (ρ.coeffTwistTransIso σ hσ τ hτ).symm (TensorAlong.tmul c m) =
      TensorAlong.tmul c (TensorAlong.tmul 1 m) :=
  ρ.baseChangeAlongCompIso_symm_tmul (σ : A →+* A) (τ : A →+* A) hσ hτ c m

/-- **The twist of a character line is the line of the twisted character**:
`(ofCharacter χ)^σ ≅ ofCharacter (σ ∘ χ)`. -/
def coeffTwistOfCharacterIso (χ : Γ →ₜ* Aˣ) :
    Iso ((ofCharacter χ).coeffTwist σ hσ)
      (ofCharacter ((ContinuousMonoidHom.unitsMap ⟨(σ : A →* A), hσ⟩).comp χ)) :=
  baseChangeAlongOfCharacterIso (σ : A →+* A) hσ χ

@[simp]
theorem coeffTwistOfCharacterIso_tmul (χ : Γ →ₜ* Aˣ) (b a : A) :
    coeffTwistOfCharacterIso σ hσ χ (TensorAlong.tmul b a) = σ a * b :=
  baseChangeAlongOfCharacterIso_tmul (σ : A →+* A) hσ χ b a

end CoeffTwist

section CoeffTwistCharpoly

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M] [Module.Free A M]
  (σ : A ≃+* A) (hσ : Continuous σ) (ρ : ContinuousRep Γ A M)

/-- The characteristic polynomial of `ρ^σ(g)` is that of `ρ(g)` with `σ` applied to its
coefficients. -/
@[simp]
theorem charpoly_coeffTwist_apply (g : Γ) :
    (ρ.coeffTwist σ hσ g).charpoly = (ρ g).charpoly.map (σ : A →+* A) :=
  ρ.charpoly_baseChangeAlong_apply (σ : A →+* A) hσ g

/-- The determinant of `ρ^σ(g)` is `σ` of that of `ρ(g)`. -/
@[simp]
theorem det_coeffTwist_apply (g : Γ) :
    LinearMap.det (ρ.coeffTwist σ hσ g) = σ (LinearMap.det (ρ g)) :=
  ρ.det_baseChangeAlong_apply (σ : A →+* A) hσ g

/-- The trace of `ρ^σ(g)` is `σ` of that of `ρ(g)`. -/
@[simp]
theorem trace_coeffTwist_apply (g : Γ) :
    LinearMap.trace A (TensorAlong (σ : A →+* A) M) (ρ.coeffTwist σ hσ g) =
      σ (LinearMap.trace A M (ρ g)) :=
  ρ.trace_baseChangeAlong_apply (σ : A →+* A) hσ g

end CoeffTwistCharpoly

section FrobTwist

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M]
  (p : ℕ) [ExpChar A p] [PerfectRing A p] (ρ : ContinuousRep Γ A M)

/-- **The Frobenius twist** `ρ^{(p)}` of a continuous representation over a perfect ring of
characteristic `p`, such as a finite field or `AlgebraicClosure (ZMod p)`: the coefficient twist by
`frobeniusEquiv A p`. -/
def frobTwist : ContinuousRep Γ A (TensorAlong (frobeniusEquiv A p : A →+* A) M) :=
  ρ.coeffTwist (frobeniusEquiv A p) (continuous_frobeniusEquiv A p)

/-- The Frobenius twist is the coefficient twist by `frobeniusEquiv A p`. -/
theorem frobTwist_eq_coeffTwist :
    ρ.frobTwist p = ρ.coeffTwist (frobeniusEquiv A p) (continuous_frobeniusEquiv A p) :=
  (rfl)

@[simp]
theorem frobTwist_apply_tmul (g : Γ) (a : A) (m : M) :
    ρ.frobTwist p g (TensorAlong.tmul a m) = TensorAlong.tmul a (ρ g m) :=
  ρ.coeffTwist_apply_tmul _ _ g a m

/-- **Entrywise formula** for the Frobenius twist: in the base-changed basis, the matrix of
`ρ^{(p)}(g)` is the matrix of `ρ(g)` with its entries raised to the `p`-th power. -/
@[simp]
theorem toMatrix_frobTwist_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A M) (g : Γ) :
    LinearMap.toMatrix (TensorAlong.basis (frobeniusEquiv A p : A →+* A) b)
        (TensorAlong.basis (frobeniusEquiv A p : A →+* A) b) (ρ.frobTwist p g) =
      (LinearMap.toMatrix b b (ρ g)).map (· ^ p) := by
  rw [frobTwist_eq_coeffTwist, toMatrix_coeffTwist_apply]
  exact Matrix.ext fun i j => frobeniusEquiv_def A p _

/-- **Over `ZMod p` the Frobenius twist is trivial**: `ρ^{(p)} ≅ ρ`, since Frobenius is the
identity of `ZMod p`. -/
def frobTwistZModIso {p : ℕ} [Fact p.Prime] [TopologicalSpace (ZMod p)]
    [IsTopologicalSemiring (ZMod p)] {M : Type*} [AddCommMonoid M] [Module (ZMod p) M]
    [TopologicalSpace M] [IsModuleTopology (ZMod p) M] [Module.Finite (ZMod p) M]
    (ρ : ContinuousRep Γ (ZMod p) M) : Iso (ρ.frobTwist p) ρ :=
  ρ.coeffTwistIsoOfEqRefl _ _ (RingEquiv.ext fun x => by
    simp [ZMod.frobenius_zmod])

/-- `frobTwistZModIso` sends `a ⊗ m` to `a • m`. -/
@[simp]
theorem frobTwistZModIso_tmul {p : ℕ} [Fact p.Prime] [TopologicalSpace (ZMod p)]
    [IsTopologicalSemiring (ZMod p)] {M : Type*} [AddCommMonoid M] [Module (ZMod p) M]
    [TopologicalSpace M] [IsModuleTopology (ZMod p) M] [Module.Finite (ZMod p) M]
    (ρ : ContinuousRep Γ (ZMod p) M) (a : ZMod p) (m : M) :
    ρ.frobTwistZModIso (TensorAlong.tmul a m) = a • m :=
  ρ.coeffTwistIsoOfEqRefl_tmul _ _ _ a m

/-- **Twisting coefficients is not conjugation**: if some value of a character `χ` is not fixed
by Frobenius, the character line is not isomorphic to its Frobenius twist, which is the line of
`χ ^ p`. -/
theorem not_nonempty_iso_frobTwist_ofCharacter (χ : Γ →ₜ* Aˣ) {g : Γ}
    (hg : (χ g : A) ^ p ≠ χ g) :
    ¬ Nonempty (Iso ((ofCharacter χ).frobTwist p) (ofCharacter χ)) := by
  rintro ⟨e⟩
  have h := (nonempty_iso_ofCharacter_iff _ _).1
    ⟨(coeffTwistOfCharacterIso (frobeniusEquiv A p) (continuous_frobeniusEquiv A p) χ).symm.trans
      e⟩
  have hχ : ((ContinuousMonoidHom.unitsMap ⟨(frobeniusEquiv A p : A →* A),
      continuous_frobeniusEquiv A p⟩).comp χ g : A) = (χ g : A) ^ p :=
    (ContinuousMonoidHom.coe_unitsMap_apply _ _).trans (frobeniusEquiv_def A p _)
  exact hg (hχ.symm.trans congr(($h g : A)))

/-- **A character with an element of order `p² - 1` in its image is not isomorphic to its
Frobenius twist**, for instance a character `χ : Γ → F_{p²}ˣ` whose image contains a generator:
the twist is `χ ^ p ≠ χ`. -/
theorem not_nonempty_iso_frobTwist_ofCharacter_of_orderOf_eq [Fact p.Prime] (χ : Γ →ₜ* Aˣ)
    {g : Γ} (hg : orderOf (χ g) = p ^ 2 - 1) :
    ¬ Nonempty (Iso ((ofCharacter χ).frobTwist p) (ofCharacter χ)) := by
  have hp := (Fact.out : p.Prime).two_le
  refine not_nonempty_iso_frobTwist_ofCharacter p χ (g := g) fun h => ?_
  -- `χ g ^ p = χ g` forces `χ g ^ (p - 1) = 1`, so `p² - 1 ∣ p - 1`, which is impossible.
  have hu : χ g ^ (p - 1) = 1 := mul_eq_right.1 <| by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact Units.ext (by simpa using h)
  have hle := Nat.le_of_dvd (by omega) (hg ▸ orderOf_dvd_of_pow_eq_one hu)
  have : p < p ^ 2 := by nlinarith
  omega

end FrobTwist

section FrobTwistCharpoly

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M] [Module.Free A M]
  (p : ℕ) [ExpChar A p] [PerfectRing A p] (ρ : ContinuousRep Γ A M)

/-- The characteristic polynomial of `ρ^{(p)}(g)` is that of `ρ(g)` with Frobenius applied to
its coefficients. -/
@[simp]
theorem charpoly_frobTwist_apply (g : Γ) :
    (ρ.frobTwist p g).charpoly = (ρ g).charpoly.map (frobenius A p) := by
  -- `frobeniusEquiv A p` is `frobenius A p` as a ring homomorphism.
  have hfrob : (frobeniusEquiv A p : A →+* A) = frobenius A p :=
    RingHom.ext (congrFun (coe_frobeniusEquiv A p))
  rw [frobTwist_eq_coeffTwist, charpoly_coeffTwist_apply, hfrob]

/-- The determinant of `ρ^{(p)}(g)` is the `p`-th power of that of `ρ(g)`. -/
@[simp]
theorem det_frobTwist_apply (g : Γ) :
    LinearMap.det (ρ.frobTwist p g) = LinearMap.det (ρ g) ^ p := by
  rw [frobTwist_eq_coeffTwist, det_coeffTwist_apply, frobeniusEquiv_def]

/-- The trace of `ρ^{(p)}(g)` is the `p`-th power of that of `ρ(g)`. -/
@[simp]
theorem trace_frobTwist_apply (g : Γ) :
    LinearMap.trace A _ (ρ.frobTwist p g) = LinearMap.trace A M (ρ g) ^ p := by
  rw [frobTwist_eq_coeffTwist, trace_coeffTwist_apply, frobeniusEquiv_def]

end FrobTwistCharpoly

end ContinuousRep

end TauCeti
