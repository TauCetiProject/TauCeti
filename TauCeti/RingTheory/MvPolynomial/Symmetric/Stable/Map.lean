/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Omega

/-!
# Change of coefficients for the symmetric functions

A ring homomorphism `f : R →+* S` of commutative semirings changes the coefficients of the
symmetric functions: applying `MvPolynomial.map f` to every member of a compatible family of
symmetric polynomials gives a compatible family over `S`. This file constructs the resulting
`f`-semilinear map in each degree and the ring homomorphism `Λ_R →+* Λ_S`, and proves that they
commute with the specializations to finite alphabets, fix the Schur, elementary, complete and
power-sum symmetric functions, act on Schur coordinates by `f`, and commute with the free
generators and the involution `ω`.

Since the Schur functions are a basis of `Λ_R` over every ring and are fixed by the change of
coefficients, the symmetric functions over `S` coming from `R` are exactly those whose Schur
coordinates come from `R` (`TauCeti.mem_range_stableSymmetricMap_iff`). For the inclusion
`ℤ → ℂ` this identifies the integral symmetric functions `Λ_ℤ` with the lattice of integral Schur
coordinates in `Λ_ℂ`, which is how virtual characters of the symmetric groups are matched with
`Λ_ℤ` under the Frobenius characteristic.

## Main definitions

* `TauCeti.stableSymmetricMap f n`: the change of coefficients along `f` for the symmetric
  functions of degree `n`, an `f`-semilinear map.
* `TauCeti.SymmetricFunction.map f`: the ring homomorphism `Λ_R →+* Λ_S` changing coefficients
  along `f`.

## Main results

* `TauCeti.SymmetricFunction.specialization_map`: changing coefficients and then specializing to
  `d` variables is specializing and then changing the coefficients of the polynomial.
* `TauCeti.stableSchurBasis_repr_stableSymmetricMap`: the Schur coordinates of the image of a
  symmetric function are the images of its Schur coordinates.
* `TauCeti.mem_range_stableSymmetricMap_iff`: a symmetric function over `S` comes from `R` exactly
  when its Schur coordinates lie in the range of `f`.
* `TauCeti.SymmetricFunction.map_injective`, `TauCeti.SymmetricFunction.map_surjective`: the change
  of coefficients is injective or surjective when `f` is.
* `TauCeti.SymmetricFunction.map_esymmAlgHom`, `TauCeti.SymmetricFunction.map_hsymmAlgHom`,
  `TauCeti.SymmetricFunction.map_omega`: naturality of the free generation by the `e_r` and by the
  `h_r`, and of `ω`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: the ring `Λ_A = Λ_ℤ ⊗ A` of symmetric functions with coefficients in a commutative
  ring `A`, and Section 3: the Schur functions form a `ℤ`-basis of `Λ`.
-/

public section

namespace TauCeti

open MvPolynomial DirectSum

section CommSemiring

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  (f : R →+* S) (g : S →+* T) {n : ℕ}

/-- The compatible family over `S` obtained by changing the coefficients of each member. -/
private noncomputable def stableSymmetricMapAux (x : stableSymmetricSubmodule R n) :
    stableSymmetricSubmodule S n :=
  ⟨fun d => ⟨MvPolynomial.map f (stableSymmetricProj R n d x),
      mem_symmetricHomogeneousSubmodule.mpr
        ⟨(mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).1.map f,
          (mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).2.map f⟩⟩,
    mem_stableSymmetricSubmodule.mpr fun d => by
      have key (p : MvPolynomial (Fin (d + 1)) R) :
          aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) S) 0) (MvPolynomial.map f p) =
            MvPolynomial.map f (aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0) p) := by
        rw [map_aeval, aeval_def, eval₂_map, coe_eval₂Hom]
        congr 1
        · ext
          simp
        · funext i
          refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
      exact (key _).trans (congrArg _ (aeval_snoc_zero_stableSymmetricProj d x))⟩

private theorem coe_stableSymmetricProj_stableSymmetricMapAux (d : ℕ)
    (x : stableSymmetricSubmodule R n) :
    (stableSymmetricProj S n d (stableSymmetricMapAux f x) : MvPolynomial (Fin d) S) =
      MvPolynomial.map f (stableSymmetricProj R n d x) := by
  rw [stableSymmetricMapAux, stableSymmetricProj_mk]

variable (n) in
/-- **Change of coefficients for the symmetric functions of degree `n`**: the `f`-semilinear map
applying `MvPolynomial.map f` to the member of a compatible family in each finite alphabet. -/
noncomputable def stableSymmetricMap :
    stableSymmetricSubmodule R n →ₛₗ[f] stableSymmetricSubmodule S n where
  toFun := stableSymmetricMapAux f
  map_add' x y := stableSymmetricSubmodule_ext fun d => Subtype.ext <| by
    simp [coe_stableSymmetricProj_stableSymmetricMapAux]
  map_smul' r x := stableSymmetricSubmodule_ext fun d => Subtype.ext <| by
    simp [coe_stableSymmetricProj_stableSymmetricMapAux, smul_eq_C_mul]

/-- **Changing coefficients is computed in each finite alphabet.** -/
@[simp]
theorem coe_stableSymmetricProj_stableSymmetricMap (d : ℕ) (x : stableSymmetricSubmodule R n) :
    (stableSymmetricProj S n d (stableSymmetricMap f n x) : MvPolynomial (Fin d) S) =
      MvPolynomial.map f (stableSymmetricProj R n d x) :=
  coe_stableSymmetricProj_stableSymmetricMapAux f d x

/-- Changing coefficients along the identity is the identity. -/
@[simp]
theorem stableSymmetricMap_id :
    stableSymmetricMap (RingHom.id R) n = LinearMap.id :=
  LinearMap.ext fun x => stableSymmetricSubmodule_ext fun d => Subtype.ext <| by
    simp [MvPolynomial.map_id]

/-- Changing coefficients along `f` and then along `g` is changing them along `g.comp f`. -/
@[simp]
theorem stableSymmetricMap_stableSymmetricMap (x : stableSymmetricSubmodule R n) :
    stableSymmetricMap g n (stableSymmetricMap f n x) = stableSymmetricMap (g.comp f) n x :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp [MvPolynomial.map_map]

/-- **Changing coefficients is injective when `f` is.** -/
theorem stableSymmetricMap_injective (hf : Function.Injective f) :
    Function.Injective (stableSymmetricMap f n) := fun x y h =>
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| map_injective f hf <| by
    rw [← coe_stableSymmetricProj_stableSymmetricMap, h,
      coe_stableSymmetricProj_stableSymmetricMap]

/-- **Changing coefficients fixes the Schur functions.** -/
@[simp]
theorem stableSymmetricMap_stableSchur (μ : n.Partition) :
    stableSymmetricMap f n (stableSchur R μ) = stableSchur S μ :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp [map_schurPoly]

/-- Changing coefficients fixes the elementary symmetric functions. -/
@[simp]
theorem stableSymmetricMap_stableEsymm :
    stableSymmetricMap f n (stableEsymm R n) = stableEsymm S n :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp [map_esymm]

/-- Changing coefficients fixes the complete homogeneous symmetric functions. -/
@[simp]
theorem stableSymmetricMap_stableHsymm :
    stableSymmetricMap f n (stableHsymm R n) = stableHsymm S n :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp [map_hsymm]

/-- Changing coefficients fixes the power sum symmetric functions. -/
@[simp]
theorem stableSymmetricMap_stablePsum (hn : n ≠ 0) :
    stableSymmetricMap f n (stablePsum R hn) = stablePsum S hn :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp [psum]

/-- Changing coefficients fixes the unit of the symmetric functions. -/
@[simp]
theorem stableSymmetricMap_stableSymmetricOne :
    stableSymmetricMap f 0 (stableSymmetricOne R) = stableSymmetricOne S :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp

/-- Changing coefficients is multiplicative in the degrees. -/
@[simp]
theorem stableSymmetricMap_stableSymmetricMul {m : ℕ} (x : stableSymmetricSubmodule R n)
    (y : stableSymmetricSubmodule R m) :
    stableSymmetricMap f (n + m) (stableSymmetricMul R n m x y) =
      stableSymmetricMul S n m (stableSymmetricMap f n x) (stableSymmetricMap f m y) :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp

namespace SymmetricFunction

/-- The additive map underlying the change of coefficients of the symmetric functions. -/
private noncomputable def mapAux : SymmetricFunction R →+ SymmetricFunction S :=
  DirectSum.map fun n => (stableSymmetricMap f n).toAddMonoidHom

private theorem specialization_mapAux (d : ℕ) (x : SymmetricFunction R) :
    specialization S d (mapAux f x) = MvPolynomial.map f (specialization R d x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [mapAux]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Change of coefficients for the symmetric functions**: the ring homomorphism `Λ_R →+* Λ_S`
applying `f` to the coefficients of the members of compatible families in all degrees. -/
noncomputable def map : SymmetricFunction R →+* SymmetricFunction S where
  __ := mapAux f
  map_one' := ext_specialization fun d => by simp [specialization_mapAux]
  map_mul' x y := ext_specialization fun d => by simp [specialization_mapAux]

/-- The change of coefficients acts on each degree by `TauCeti.stableSymmetricMap`. -/
@[simp]
theorem map_apply (x : SymmetricFunction R) (n : ℕ) :
    map f x n = stableSymmetricMap f n (x n) :=
  DirectSum.map_apply (fun n => (stableSymmetricMap f n).toAddMonoidHom) n x

/-- The change of coefficients of a symmetric function of degree `n`. -/
@[simp]
theorem map_of (x : stableSymmetricSubmodule R n) :
    map f (DirectSum.of _ n x) = DirectSum.of _ n (stableSymmetricMap f n x) :=
  DirectSum.map_of (fun n => (stableSymmetricMap f n).toAddMonoidHom) n x

/-- **Changing coefficients commutes with specialization**: in `d` variables, the change of
coefficients of a symmetric function is the change of coefficients of the polynomial. -/
@[simp]
theorem specialization_map (d : ℕ) (x : SymmetricFunction R) :
    specialization S d (map f x) = MvPolynomial.map f (specialization R d x) :=
  specialization_mapAux f d x

/-- Changing coefficients along the identity is the identity. -/
@[simp]
theorem map_id : map (RingHom.id R) = RingHom.id (SymmetricFunction R) :=
  RingHom.ext fun x => ext_specialization fun d => by simp [MvPolynomial.map_id]

/-- Changing coefficients along `f` and then along `g` is changing them along `g.comp f`. -/
@[simp]
theorem map_map (x : SymmetricFunction R) : map g (map f x) = map (g.comp f) x :=
  ext_specialization fun d => by simp [MvPolynomial.map_map]

/-- Changing coefficients along `f` and then along `g` is changing them along `g.comp f`. -/
theorem map_comp_map : (map g).comp (map f) = map (g.comp f) :=
  RingHom.ext (map_map f g)

/-- **Changing coefficients sends a scalar to its image under `f`.** -/
@[simp]
theorem map_algebraMap (r : R) :
    map f (algebraMap R (SymmetricFunction R) r) = algebraMap S (SymmetricFunction S) (f r) :=
  ext_specialization fun d => by simp

/-- **The change of coefficients is injective when `f` is.** -/
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) :=
  (DirectSum.map_injective _).2 fun _ => stableSymmetricMap_injective f hf

/-- **Changing coefficients commutes with the free generation by the elementary symmetric
functions**: it changes the coefficients of the polynomial in the generators. -/
@[simp]
theorem map_esymmAlgHom (p : MvPolynomial ℕ R) :
    map f (esymmAlgHom R p) = esymmAlgHom S (MvPolynomial.map f p) := by
  have h : (map f).comp (esymmAlgHom R).toRingHom =
      (esymmAlgHom S).toRingHom.comp (MvPolynomial.map f) :=
    MvPolynomial.ringHom_ext (fun r => by simp [← algebraMap_eq])
      (fun r => by simp)
  exact DFunLike.congr_fun h p

/-- **Changing coefficients commutes with the free generation by the complete homogeneous
symmetric functions**: it changes the coefficients of the polynomial in the generators. -/
@[simp]
theorem map_hsymmAlgHom (p : MvPolynomial ℕ R) :
    map f (hsymmAlgHom R p) = hsymmAlgHom S (MvPolynomial.map f p) := by
  have h : (map f).comp (hsymmAlgHom R).toRingHom =
      (hsymmAlgHom S).toRingHom.comp (MvPolynomial.map f) :=
    MvPolynomial.ringHom_ext (fun r => by simp [← algebraMap_eq])
      (fun r => by simp)
  exact DFunLike.congr_fun h p

end SymmetricFunction

end CommSemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}

/-- The change of coefficients of the symmetric function of degree `n` with prescribed Schur
coordinates in `R`. -/
private theorem stableSymmetricMap_sum_smul_stableSchur (c : n.Partition → R) :
    stableSymmetricMap f n (∑ μ, c μ • stableSchur R μ) = ∑ μ, f (c μ) • stableSchur S μ := by
  simp [map_smulₛₗ]

/-- **Changing coefficients acts on Schur coordinates by `f`.** -/
@[simp]
theorem stableSchurBasis_repr_stableSymmetricMap (x : stableSymmetricSubmodule R n)
    (μ : n.Partition) :
    (stableSchurBasis S n).repr (stableSymmetricMap f n x) μ =
      f ((stableSchurBasis R n).repr x μ) := by
  have h := stableSymmetricMap_sum_smul_stableSchur f ((stableSchurBasis R n).repr x)
  simp only [← stableSchurBasis_apply, Module.Basis.sum_repr] at h
  rw [h, Module.Basis.repr_sum_self]

/-- **A symmetric function over `S` comes from `R` exactly when its Schur coordinates lie in the
range of `f`.** For the inclusion `ℤ → ℂ`, the integral symmetric functions are the lattice of
integral Schur coordinates. -/
theorem mem_range_stableSymmetricMap_iff {y : stableSymmetricSubmodule S n} :
    y ∈ Set.range (stableSymmetricMap f n) ↔
      ∀ μ, (stableSchurBasis S n).repr y μ ∈ f.range := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨x, rfl⟩ μ
    simp
  · choose c hc using h
    refine ⟨∑ μ, c μ • stableSchur R μ, ?_⟩
    rw [stableSymmetricMap_sum_smul_stableSchur]
    conv_rhs => rw [← (stableSchurBasis S n).sum_repr y]
    simp [hc]

/-- **Changing coefficients is surjective when `f` is.** -/
theorem stableSymmetricMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (stableSymmetricMap f n) := fun _ =>
  (mem_range_stableSymmetricMap_iff f).2 fun _ => hf _

namespace SymmetricFunction

/-- **The change of coefficients is surjective when `f` is.** -/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) :=
  (DirectSum.map_surjective _).2 fun _ => stableSymmetricMap_surjective f hf

/-- **Changing coefficients commutes with the involution `ω`.** -/
@[simp]
theorem map_omega (x : SymmetricFunction R) : map f (omega R x) = omega S (map f x) := by
  obtain ⟨p, rfl⟩ := esymmAlgHom_surjective R x
  rw [omega_esymmAlgHom, map_hsymmAlgHom, map_esymmAlgHom, omega_esymmAlgHom]

end SymmetricFunction

end CommRing

end TauCeti
