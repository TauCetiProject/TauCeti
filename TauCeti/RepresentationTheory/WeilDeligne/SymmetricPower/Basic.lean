/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Derivation
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.RepresentationTheory.Intertwining
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
carries the isomorphism `D ≅ D.transport e` to an isomorphism of symmetric powers, so the symmetric
power of a transport is the transport of the symmetric power. The zeroth
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
* `TauCeti.WeilDeligneParameter.sym_transport`: the symmetric power commutes with transport.
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
  isOpen_ker := Subgroup.isOpen_mono (D.r.ker_le_ker_symmetricPower m) D.isOpen_ker
  N := SymmetricPower.differential E V m D.N
  isNilpotent_N := SymmetricPower.isNilpotent_differential m D.isNilpotent_N
  conj_N w := Representation.mul_mul_inv_eq_smul_of_mul_eq_smul_mul <| by
    simpa [Module.End.mul_eq_comp, LinearMap.smul_comp] using
      SymmetricPower.map_comp_differential m (f := D.r w) (Y := (q : E) ^ (deg w).toAdd • D.N)
        (by simpa [Module.End.mul_eq_comp, LinearMap.smul_comp] using D.r_mul_N w)

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

@[simp]
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
  simp

@[simp]
theorem Hom.sym_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) :
    (f.comp g).sym m = (f.sym m).comp (g.sym m) := by
  ext1
  simp

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
theorem Iso.sym_toLinearEquiv (f : Iso D₁ D₂) :
    (f.sym m).toLinearEquiv = SymmetricPower.congr f.toLinearEquiv :=
  Representation.Equiv.symmetricPower_toLinearEquiv ..

@[simp]
theorem Iso.toHom_sym (f : Iso D₁ D₂) : (f.sym m).toHom = f.toHom.sym m := by
  ext1
  rw [Iso.toHom_toLinearMap, Hom.sym_toLinearMap, Iso.toHom_toLinearMap]
  exact Representation.Equiv.symmetricPower_toLinearMap ..

@[simp]
theorem Iso.sym_refl : (Iso.refl D₁).sym m = Iso.refl (D₁.sym m) :=
  Iso.ext <| LinearEquiv.toLinearMap_injective <| SymmetricPower.ext fun v ↦ by simp

@[simp]
theorem Iso.sym_trans (f : Iso D₁ D₂) (g : Iso D₂ D₃) :
    (f.trans g).sym m = (f.sym m).trans (g.sym m) :=
  Iso.ext <| LinearEquiv.toLinearMap_injective <| SymmetricPower.ext fun v ↦ by simp

@[simp]
theorem Iso.sym_symm (f : Iso D₁ D₂) : f.symm.sym m = (f.sym m).symm :=
  Iso.ext <| by simp

/-- **The symmetric power commutes with transport**: `Sym^m (e_* D) = (Sym^m e)_* (Sym^m D)`, where
`Sym^m e = SymmetricPower.congr e` sends `⨂ₛ v` to `⨂ₛ (e ∘ v)`. -/
theorem sym_transport (e : V ≃ₗ[E] V₁) :
    (D.transport e).sym m = (D.sym m).transport (SymmetricPower.congr e) := by
  have h : ((D.transportIso e).sym m).toLinearEquiv = SymmetricPower.congr e := by simp
  exact h ▸ ((D.transportIso e).sym m).eq_transport

/-! ### Low symmetric powers, twists and zero monodromy -/

/-- The zeroth symmetric power has trivial Weil action. -/
theorem sym_zero_r (w : W) : (D.sym 0).r w = 1 := by
  simp

/-- The zeroth symmetric power has zero monodromy. -/
theorem sym_zero_N : (D.sym 0).N = 0 := by
  simp

/-- `Sym^m ∘ (r, 0)` has zero monodromy. -/
theorem sym_N_eq_zero (h : D.N = 0) : (D.sym m).N = 0 := by
  rw [sym_N, h, map_zero]

/-- **The first symmetric power is the parameter itself**: `Sym^1 ∘ D ≅ D`, through
`Sym[E]^1 V ≃ V`, `v ↦ v`, the identification of `Sym[E]^1 V` with the degree-one part of the
symmetric algebra (`SymmetricPower.equivHomogeneous`), which is `V`
(`TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv`). -/
def symOneIso : Iso (D.sym 1) D where
  toRepresentationEquiv := .mk ((SymmetricPower.equivHomogeneous 1).trans
      (TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv E V)) fun w ↦
    SymmetricPower.ext fun v ↦ by simp [Representation.symmetricPower_apply]
  comp_N := SymmetricPower.ext fun v ↦ by simp

@[simp]
theorem symOneIso_tprod (v : Fin 1 → V) : D.symOneIso (⨂ₛ[E] i, v i) = v 0 :=
  by simp [symOneIso]

@[simp]
theorem symOneIso_symm_apply (v : V) : D.symOneIso.symm v = ⨂ₛ[E] _ : Fin 1, v :=
  D.symOneIso.injective <| by simp

/-- **Symmetric powers of twists**: `Sym^m (D ⊗ χ) = Sym^m D ⊗ χ ^ m`. -/
theorem sym_twist (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) :
    (D.twist χ hχ).sym m = (D.sym m).twist (χ ^ m)
      (Subgroup.isOpen_mono (fun w hw ↦ by simp_all [MonoidHom.mem_ker]) hχ) := by
  refine WeilDeligneParameter.ext ?_ (by simp)
  ext w : 1
  refine SymmetricPower.ext fun v ↦ ?_
  simp [Representation.symmetricPower_apply, MultilinearMap.map_smul_univ]

end WeilDeligneParameter

end TauCeti
