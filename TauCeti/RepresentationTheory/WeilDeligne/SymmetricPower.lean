/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Derivation
public import TauCeti.LinearAlgebra.SymmetricPower.Lift
public import TauCeti.RepresentationTheory.SymmetricPower
public import TauCeti.RepresentationTheory.WeilDeligne.Operations

/-!
# Symmetric powers of raw Weil–Deligne parameters

For a raw Weil–Deligne parameter `(V, r, N)` (`TauCeti.WeilDeligneParameter`) and `m : ℕ`, the
`m`-th symmetric power `Sym^m ∘ (r, N)` is the parameter on Mathlib's symmetric tensor power
`Sym[E]^m V` with Weil action `Sym^m ∘ r` (`Representation.symmetricPower`) and monodromy the
differential `d Sym^m (N)` (`SymmetricPower.differential`), which sends `v₁ ⋯ v_m` to
`∑ⱼ v₁ ⋯ (N vⱼ) ⋯ v_m`. The differential of a nilpotent endomorphism is nilpotent, and the
conjugation relation follows from the naturality of the differential
(`SymmetricPower.map_comp_differential`): `Sym^m (r w)` carries `d Sym^m (N)` to
`d Sym^m (r(w) N r(w)⁻¹) = q ^ deg w • d Sym^m (N)`.

The construction is functorial on morphisms and isomorphisms of parameters; in particular it
carries the isomorphism `D ≅ D.transport e` to an isomorphism of symmetric powers. The zeroth
symmetric power has trivial Weil action and zero monodromy, the first is isomorphic to the
parameter itself, a twist by `χ` becomes a twist by `χ ^ m`, and zero monodromy stays zero.

## Main definitions

* `TauCeti.WeilDeligneParameter.sym D m`: the `m`-th symmetric power of `D`.
* `TauCeti.WeilDeligneParameter.Hom.sym`, `TauCeti.WeilDeligneParameter.Iso.sym`: symmetric
  powers of morphisms and isomorphisms.
* `TauCeti.WeilDeligneParameter.symOneIso`: `Sym^1 ∘ D ≅ D`.

## Main results

* `TauCeti.WeilDeligneParameter.Hom.sym_id`, `TauCeti.WeilDeligneParameter.Hom.sym_comp`, and
  their counterparts for isomorphisms: the symmetric power is functorial.
* `TauCeti.WeilDeligneParameter.sym_zero_r`, `TauCeti.WeilDeligneParameter.sym_zero_N`: the
  zeroth symmetric power is the trivial parameter.
* `TauCeti.WeilDeligneParameter.sym_twist`: `Sym^m (D ⊗ χ) = Sym^m D ⊗ χ ^ m`.
* `TauCeti.WeilDeligneParameter.sym_N_eq_zero`: `Sym^m ∘ (r, 0)` has zero monodromy.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct

namespace WeilDeligneParameter

variable {E : Type} [Field E] {W V V₁ V₂ V₃ : Type*} [Group W] [TopologicalSpace W]
  [SeparatelyContinuousMul W] [AddCommGroup V] [Module E V]
  [AddCommGroup V₁] [Module E V₁] [AddCommGroup V₂] [Module E V₂] [AddCommGroup V₃] [Module E V₃]
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- The **`m`-th symmetric power** `(Sym^m V, Sym^m ∘ r, d Sym^m (N))` of a raw Weil–Deligne
parameter. -/
def sym (D : WeilDeligneParameter E W V deg q) (m : ℕ) :
    WeilDeligneParameter E W (Sym[E]^m V) deg q where
  r := D.r.symmetricPower m
  isOpen_ker := Subgroup.isOpen_mono (fun w hw ↦ by
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [Representation.symmetricPower_apply, hw, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]) D.isOpen_ker
  N := SymmetricPower.differential E V m D.N
  isNilpotent_N := SymmetricPower.isNilpotent_differential m D.isNilpotent_N
  conj_N w := by
    have h : D.r w ∘ₗ D.N = ((q : E) ^ (deg w).toAdd • D.N) ∘ₗ D.r w := by
      rw [← D.conj_N w, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc,
        LinearMap.comp_assoc, ← Module.End.mul_eq_comp (D.r w⁻¹), ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_eq_id, LinearMap.comp_id]
    have h' := SymmetricPower.map_comp_differential m h
    rw [map_smul] at h'
    have hinv : SymmetricPower.map (ι := Fin m) (D.r w) ∘ₗ SymmetricPower.map (D.r w⁻¹) =
        LinearMap.id := by
      rw [← SymmetricPower.map_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_eq_id, SymmetricPower.map_id]
    rw [Representation.symmetricPower_apply, Representation.symmetricPower_apply,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, h', LinearMap.comp_assoc, hinv,
      LinearMap.comp_id]

variable (D : WeilDeligneParameter E W V deg q) (m : ℕ)

@[simp]
theorem sym_r : (D.sym m).r = D.r.symmetricPower m :=
  (rfl)

@[simp]
theorem sym_N : (D.sym m).N = SymmetricPower.differential E V m D.N :=
  (rfl)

variable {D₁ : WeilDeligneParameter E W V₁ deg q} {D₂ : WeilDeligneParameter E W V₂ deg q}
  {D₃ : WeilDeligneParameter E W V₃ deg q}

/-- The `m`-th symmetric power of a morphism of parameters. -/
def Hom.sym (f : Hom D₁ D₂) : Hom (D₁.sym m) (D₂.sym m) where
  toIntertwiningMap := f.toIntertwiningMap.symmetricPower m
  comp_N := by
    rw [Representation.IntertwiningMap.symmetricPower_toLinearMap]
    exact SymmetricPower.map_comp_differential m f.comp_N

theorem Hom.sym_toLinearMap (f : Hom D₁ D₂) :
    (f.sym m).toLinearMap = SymmetricPower.map (ι := Fin m) f.toLinearMap :=
  Representation.IntertwiningMap.symmetricPower_toLinearMap ..

@[simp]
theorem Hom.sym_tprod (f : Hom D₁ D₂) (v : Fin m → V₁) :
    f.sym m (⨂ₛ[E] i, v i) = ⨂ₛ[E] i, f (v i) :=
  Representation.IntertwiningMap.symmetricPower_apply_tprod ..

@[simp]
theorem Hom.sym_id : (Hom.id D₁).sym m = Hom.id (D₁.sym m) := by
  ext1
  rw [Hom.sym_toLinearMap, Hom.id_toLinearMap, Hom.id_toLinearMap, SymmetricPower.map_id]

@[simp]
theorem Hom.sym_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) :
    (f.comp g).sym m = (f.sym m).comp (g.sym m) := by
  ext1
  rw [Hom.sym_toLinearMap, Hom.comp_toLinearMap, Hom.comp_toLinearMap, Hom.sym_toLinearMap,
    Hom.sym_toLinearMap, SymmetricPower.map_comp]

/-- The `m`-th symmetric power of an isomorphism of parameters. -/
def Iso.sym (f : Iso D₁ D₂) : Iso (D₁.sym m) (D₂.sym m) where
  toRepresentationEquiv := f.toRepresentationEquiv.symmetricPower m
  comp_N := by
    have h := (f.toHom.sym m).comp_N
    rw [Hom.sym_toLinearMap, Iso.toHom_toLinearMap,
      ← Representation.Equiv.symmetricPower_toLinearMap] at h
    exact h

@[simp]
theorem Iso.sym_tprod (f : Iso D₁ D₂) (v : Fin m → V₁) :
    f.sym m (⨂ₛ[E] i, v i) = ⨂ₛ[E] i, f (v i) :=
  Representation.Equiv.symmetricPower_apply_tprod ..

@[simp]
theorem Iso.toHom_sym (f : Iso D₁ D₂) : (f.sym m).toHom = f.toHom.sym m := by
  ext1
  rw [Iso.toHom_toLinearMap, Hom.sym_toLinearMap, Iso.toHom_toLinearMap]
  exact Representation.Equiv.symmetricPower_toLinearMap ..

private theorem Iso.sym_toRepresentationEquiv (f : Iso D₁ D₂) :
    (f.sym m).toRepresentationEquiv = f.toRepresentationEquiv.symmetricPower m :=
  (rfl)

@[simp]
theorem Iso.sym_refl : (Iso.refl D₁).sym m = Iso.refl (D₁.sym m) := by
  ext1
  rw [Iso.sym_toRepresentationEquiv, Iso.refl_toRepresentationEquiv,
    Representation.Equiv.symmetricPower_refl, Iso.refl_toRepresentationEquiv]
  rfl

@[simp]
theorem Iso.sym_trans (f : Iso D₁ D₂) (g : Iso D₂ D₃) :
    (f.trans g).sym m = (f.sym m).trans (g.sym m) := by
  ext1
  rw [Iso.sym_toRepresentationEquiv, Iso.trans_toRepresentationEquiv,
    Representation.Equiv.symmetricPower_trans, Iso.trans_toRepresentationEquiv]
  rfl

@[simp]
theorem Iso.sym_symm (f : Iso D₁ D₂) : f.symm.sym m = (f.sym m).symm := by
  ext1
  rw [Iso.sym_toRepresentationEquiv, Iso.symm_toRepresentationEquiv,
    Representation.Equiv.symmetricPower_symm, Iso.symm_toRepresentationEquiv]
  rfl

/-! ### Low symmetric powers, twists and zero monodromy -/

/-- The zeroth symmetric power has trivial Weil action. -/
theorem sym_zero_r (w : W) : (D.sym 0).r w = 1 :=
  SymmetricPower.ext fun v ↦ by
    simp [Representation.symmetricPower_apply, Subsingleton.elim (fun i ↦ D.r w (v i)) v]

/-- The zeroth symmetric power has zero monodromy. -/
theorem sym_zero_N : (D.sym 0).N = 0 :=
  SymmetricPower.ext fun v ↦ by simp

/-- `Sym^m ∘ (r, 0)` has zero monodromy. -/
theorem sym_N_eq_zero (h : D.N = 0) : (D.sym m).N = 0 := by
  rw [sym_N, h, map_zero]

/-- The first symmetric power `Sym[E]^1 V` is `V`, through `v ↦ v`. -/
private def symOneLinearEquiv : (Sym[E]^1 V) ≃ₗ[E] V :=
  LinearEquiv.ofLinearMap
    (SymmetricPower.lift (MultilinearMap.ofSubsingleton (RingHom.id E) V V 0 LinearMap.id)
      fun e ↦ by
        ext v
        simpa using congrArg v (Subsingleton.elim (e 0) 0))
    ((SymmetricPower.mk E (Fin 1) V).comp
      (PiTensorProduct.subsingletonEquiv (R := E) (s := fun _ : Fin 1 ↦ V) 0).symm.toLinearMap)
    (LinearMap.ext fun v ↦ by simp [PiTensorProduct.subsingletonEquiv])
    (SymmetricPower.ext fun v ↦ by
      have h : (PiTensorProduct.subsingletonEquiv (R := E) (s := fun _ : Fin 1 ↦ V) 0).symm
          (v 0) = PiTensorProduct.tprod E v :=
        (LinearEquiv.symm_apply_eq _).2 (PiTensorProduct.subsingletonEquiv_apply_tprod _ v).symm
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
        SymmetricPower.lift_tprod, MultilinearMap.ofSubsingleton_apply_apply, LinearMap.id_apply, h]
      rfl)

private theorem symOneLinearEquiv_tprod (v : Fin 1 → V) :
    symOneLinearEquiv (⨂ₛ[E] i, v i) = v 0 := by
  simp [symOneLinearEquiv]

/-- **The first symmetric power is the parameter itself**: `Sym^1 ∘ D ≅ D`, through
`Sym[E]^1 V ≃ V`, `v ↦ v`. -/
def symOneIso : Iso (D.sym 1) D where
  toRepresentationEquiv := .mk symOneLinearEquiv fun w ↦ SymmetricPower.ext fun v ↦ by
    simp [symOneLinearEquiv_tprod, Representation.symmetricPower_apply]
  comp_N := SymmetricPower.ext fun v ↦ by
    simp [symOneLinearEquiv_tprod]

@[simp]
theorem symOneIso_tprod (v : Fin 1 → V) : D.symOneIso (⨂ₛ[E] i, v i) = v 0 :=
  symOneLinearEquiv_tprod v

/-- **Symmetric powers of twists**: `Sym^m (D ⊗ χ) = Sym^m D ⊗ χ ^ m`. -/
theorem sym_twist (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W))
    (hχm : IsOpen ((χ ^ m).ker : Set W)) :
    (D.twist χ hχ).sym m = (D.sym m).twist (χ ^ m) hχm := by
  refine WeilDeligneParameter.ext ?_ (by rw [sym_N, twist_N, twist_N, sym_N])
  ext w : 1
  refine SymmetricPower.ext fun v ↦ ?_
  simp [Representation.symmetricPower_apply, MultilinearMap.map_smul_univ]

end WeilDeligneParameter

end TauCeti
