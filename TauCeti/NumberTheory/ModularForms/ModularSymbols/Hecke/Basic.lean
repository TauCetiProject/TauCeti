/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
public import TauCeti.NumberTheory.HeckeRing.Representation
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic

/-!
# Hecke operators on modular symbols

An integral matrix `δ ∈ GL(2, ℚ)` acts on `Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)` by
`δ · ({α, β} ⊗ P) = {δα, δβ} ⊗ (P ∣ adj δ)`,
the Möbius action on the cusps tensored with the adjugate action `TauCeti.binaryFormAdjugateRep`
on binary forms (`TauCeti.ModularSymbols.symbolIntRep`). On `SL(2, ℤ)` the adjugate is the
inverse, so this extends the action `TauCeti.ModularSymbols.symbolRep` through which the module
of modular symbols `𝕄_w(Γ; R)` is defined as coinvariants. It is the action adjoint to Mathlib's
weight-`w + 2` slash action under the period pairing
`∫_β^α f(z) P(z, 1) dz`: substituting `z ↦ δz` gives
`⟪f ∣[k] δ, {α, β} ⊗ P⟫ = ⟪f, δ · ({α, β} ⊗ P)⟫` with no determinant factor.

For a double coset `D = Γ₁' δ Γ₂'` of a Hecke triple in `GL(2, ℚ)` whose flanks are the images
`Γᵢ' = Γᵢ.map (mapGL ℚ)` of subgroups `Γ₁, Γ₂ ≤ SL(2, ℤ)`, decomposed into right cosets
`Γ₁' δ Γ₂' = ⊔ᵥ Γ₁' aᵥ`, the **Hecke operator** on modular symbols is
`T_D : 𝕄_w(Γ₂; R) → 𝕄_w(Γ₁; R)`, `{α, β} ⊗ P ↦ ∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)`
(`TauCeti.ModularSymbols.heckeSymbol`). It is well defined because right multiplication by
`Γ₂'` permutes the right cosets (`HeckeCoset.heckeSum_comp_of_mem`), and it is independent of
the representatives chosen (`heckeSymbol_symbol_eq_sum_of_rightCosets`). Taking `Γ₁ = Γ₂ = Γ₁(N)`
and the double coset of `diag(1, n)` gives the Hecke operator `T_n` on `𝕄_w(Γ₁(N); R)`
(`TauCeti.ModularSymbols.heckeTSymbol`), the operator of the same double coset as `T_n` on
modular forms. Over `R = ℤ` these are endomorphisms of a finitely generated abelian group, which
is the integrality of the Hecke action that makes the Hecke eigenvalues of cusp forms algebraic
integers once the period pairing is shown to be Hecke-equivariant and injective.

## Main definitions

* `TauCeti.ModularSymbols.symbolIntRep R w`: the action of the integral matrices `intEntries 2`
  on `Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)`, extending `TauCeti.ModularSymbols.symbolRep`.
* `TauCeti.ModularSymbols.heckeSymbol Γ₁ Γ₂ D hD`: the Hecke operator
  `𝕄_w(Γ₂; R) →ₗ[R] 𝕄_w(Γ₁; R)` of a double coset `D` whose representative `D.out` is an
  integral matrix.
* `TauCeti.ModularSymbols.heckeTSymbol N n`: the Hecke operator `T_n` on `𝕄_w(Γ₁(N); R)`.

## Main results

* `TauCeti.ModularSymbols.symbolIntRep_mapGL`: on `SL(2, ℤ)` the action is `symbolRep`, and
  `TauCeti.ModularSymbols.mk_symbolIntRep_eq_of_rightCoset_eq`: the class of `δ · x` in
  `𝕄_w(Γ₁; R)` depends only on the right coset `Γ₁' δ`.
* `TauCeti.ModularSymbols.heckeSymbol_symbol`: the formula
  `T_D ({α, β} ⊗ P) = ∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)` over the chosen representatives, and
  `TauCeti.ModularSymbols.heckeSymbol_symbol_eq_sum_of_rightCosets`, the same formula over any
  family of representatives of the right cosets.
* `TauCeti.ModularSymbols.heckeSymbol_one`: the identity double coset acts as the identity, and
  `TauCeti.ModularSymbols.heckeTSymbol_one`: `T₁ = 1`.
* `TauCeti.ModularSymbols.heckeTSymbol_congr`: `T_n` transported along an equality of indices,
  each carrying its own `NeZero` instance.

## References

* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §2.
* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 and §8.2.
-/

public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix MulOpposite MvPolynomial Representation
  TensorProduct
open Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w : ℕ}

/-! ### The action of integral matrices on `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)` -/

variable (R w) in
/-- **The action of integral matrices on `Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)`**:
`δ · (D ⊗ P) = δD ⊗ (P ∣ adj δ)`, the Möbius action on the cusps tensored with the adjugate
action on binary forms, as a representation of the monoid `intEntries 2` of invertible integral
matrices. On `SL(2, ℤ)` it is `TauCeti.ModularSymbols.symbolRep` (`symbolIntRep_mapGL`). -/
noncomputable def symbolIntRep :
    Representation R (intEntries 2) (degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :=
  Representation.tprod ((degreeZeroGLRep R).comp (intEntries 2).subtype)
    ((binaryFormAdjugateRep R w).comp (intMatrix 2))

@[simp]
theorem symbolIntRep_tmul (δ : intEntries 2) (D : degreeZero R)
    (P : homogeneousSubmodule (Fin 2) R w) :
    symbolIntRep R w δ (D ⊗ₜ P) =
      degreeZeroGLRep R δ D ⊗ₜ binaryFormAdjugateRep R w (intMatrix 2 δ) P := by
  simp [symbolIntRep]

/-- On `SL(2, ℤ)` the action of integral matrices is the action `symbolRep` defining the modular
symbols. -/
@[simp]
theorem symbolIntRep_mapGL (γ : SL(2, ℤ)) :
    symbolIntRep R w ⟨mapGL ℚ γ, mapGL_mem_intEntries 2 γ⟩ = symbolRep R w γ := by
  refine TensorProduct.ext' fun D P ↦ ?_
  rw [symbolIntRep_tmul, symbolRep_tmul, degreeZeroRep_apply, intMatrix_mapGL,
    binaryFormAdjugateRep_coe]

/-- The class of `δ · (([α] - [β]) ⊗ P)` in `𝕄_w(Γ; R)` is the symbol
`{δα, δβ} ⊗ (P ∣ adj δ)`. -/
theorem mk_symbolIntRep_tmul (Γ : Subgroup SL(2, ℤ)) (δ : intEntries 2) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ w)
        (symbolIntRep R w δ (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ P)) =
      symbol Γ ((δ : GL (Fin 2) ℚ) • α) ((δ : GL (Fin 2) ℚ) • β)
        (binaryFormRep R w (op (adjugate (intMatrix 2 δ))) P) := by
  rw [symbolIntRep_tmul, symbol_apply, binaryFormAdjugateRep_apply]
  rw [degreeZeroGLRep_single_sub_single]

/-! ### The Hecke operator of a double coset -/

variable (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (hD : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2)

/-- The projection onto `𝕄_w(Γ₁; R)` is invariant under the action of `Γ₁.map (mapGL ℚ)`
through `symbolIntRep`: that action is `symbolRep`, which the coinvariants kill. -/
theorem mk_comp_symbolIntRep_of_mem {γ : GL (Fin 2) ℚ} (hγ : γ ∈ Γ₁.map (mapGL ℚ)) :
    (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w) ∘ₗ symbolIntRep R w ⟨γ, map_mapGL_le_intEntries 2 Γ₁ hγ⟩ =
      Coinvariants.mk _ := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [symbolIntRep_mapGL]
  refine LinearMap.ext fun x ↦ ?_
  exact Coinvariants.mk_self_apply _ (⟨g, hg⟩ : Γ₁) x

/-- **The class of `δ · x` in `𝕄_w(Γ₁; R)` depends only on the right coset `Γ₁' δ`.** If
`Γ₁' δ₁ = Γ₁' δ₂` then `δ₂ = (δ₂ δ₁⁻¹) δ₁` with `δ₂ δ₁⁻¹ ∈ Γ₁'` — so `δ₂` is integral along with
`δ₁` (`HeckeRing.GLn.mem_intEntries_of_rightCoset_eq`) — and the coinvariants do not see that
factor. -/
theorem mk_symbolIntRep_eq_of_rightCoset_eq {δ₁ δ₂ : GL (Fin 2) ℚ} (h₁ : δ₁ ∈ intEntries 2)
    (h : op δ₁ • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) =
      op δ₂ • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w) (symbolIntRep R w ⟨δ₁, h₁⟩ x) =
      Coinvariants.mk _ (symbolIntRep R w ⟨δ₂, mem_intEntries_of_rightCoset_eq 2 h₁ h⟩ x) :=
  LinearMap.congr_fun (HeckeCoset.comp_eq_of_rightCoset_eq (symbolIntRep R w)
    (map_mapGL_le_intEntries 2 Γ₁) (fun _ hγ ↦ mk_comp_symbolIntRep_of_mem Γ₁ hγ) h₁
    (mem_intEntries_of_rightCoset_eq 2 h₁ h) h) x

variable [Finite (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- The enumeration `∑` needs, obtained from the `Finite` assumption by choice exactly as in
`HeckeRing/Representation.lean`, so that the sums below are the terms `heckeSum_apply` produces.
It is `local` and `noncomputable`: no declaration in this file depends on which enumeration is
chosen. -/
noncomputable local instance :
    Fintype (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The Hecke operator of a double coset on modular symbols.** For `D = Γ₁' δ Γ₂' = ⊔ᵥ Γ₁' aᵥ`
with `Γᵢ' = Γᵢ.map (mapGL ℚ)`, this is the `R`-linear map `𝕄_w(Γ₂; R) → 𝕄_w(Γ₁; R)` sending
`{α, β} ⊗ P` to `∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)` (`heckeSymbol_symbol`). It is the descent to the
`Γ₂`-coinvariants of the Hecke sum `HeckeCoset.heckeSum` of `D` on `symbolIntRep`, and it depends
on the double coset alone, not on the representatives (`heckeSymbol_symbol_eq_sum_of_rightCosets`).

The hypothesis `hD` is what lets the representatives act integrally: the chosen `D.out` is an
integral matrix, and `Γ₂` consists of them, so every representative does
(`DoubleCoset.rightCosetRep_mem`). Nothing is asked of the rest of `Δ`; for the double cosets of
the modular-forms theory the hypothesis is supplied by `Delta0_le_intEntries`. -/
noncomputable def heckeSymbol : ModularSymbols R Γ₂ w →ₗ[R] ModularSymbols R Γ₁ w :=
  Coinvariants.lift _
    (HeckeCoset.heckeSum D (symbolIntRep R w) hD (map_mapGL_le_intEntries 2 Γ₂)
      (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w))
    fun γ ↦ by
      have h := HeckeCoset.heckeSum_comp_of_mem D (symbolIntRep R w) hD
        (map_mapGL_le_intEntries 2 Γ₂) (map_mapGL_le_intEntries 2 Γ₁)
        (fun _ hγ ↦ mk_comp_symbolIntRep_of_mem Γ₁ hγ) (Subgroup.mem_map_of_mem (mapGL ℚ) γ.2)
      rwa [symbolIntRep_mapGL] at h

/-- On the class of `x`, the Hecke operator is the Hecke sum `HeckeCoset.heckeSum` of the double
coset on `symbolIntRep`, relative to the projection onto `𝕄_w(Γ₁; R)`: the defining equation of
`heckeSymbol`, which is a lift out of the coinvariants. -/
theorem heckeSymbol_mk_eq_heckeSum (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D hD (Coinvariants.mk _ x) =
      HeckeCoset.heckeSum D (symbolIntRep R w) hD (map_mapGL_le_intEntries 2 Γ₂)
        (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
          ModularSymbols R Γ₁ w) x :=
  Coinvariants.lift_mk _ _ _ x

/-- The Hecke operator on the class of `x ∈ Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`: the sum of the classes of
the translates `aᵥ · x` over the chosen right-coset representatives. -/
theorem heckeSymbol_mk (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D hD (Coinvariants.mk _ x) =
      ∑ v, (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨rightCosetRep D v,
          rightCosetRep_mem D hD (map_mapGL_le_intEntries 2 Γ₂) v⟩ x) := by
  rw [heckeSymbol_mk_eq_heckeSum, HeckeCoset.heckeSum_apply]

/-- **The Hecke operator on a modular symbol**, over the chosen representatives:
`T_D ({α, β} ⊗ P) = ∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)`. -/
theorem heckeSymbol_symbol (α β : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D hD (symbol Γ₂ α β P) =
      ∑ v, symbol Γ₁ (rightCosetRep D v • α) (rightCosetRep D v • β)
        (binaryFormRep R w (op (adjugate (intMatrix 2 ⟨rightCosetRep D v,
          rightCosetRep_mem D hD (map_mapGL_le_intEntries 2 Γ₂) v⟩))) P) := by
  rw [symbol_apply, heckeSymbol_mk]
  exact Finset.sum_congr rfl fun v _ ↦ mk_symbolIntRep_tmul Γ₁ _ α β P

/-- **The Hecke operator on the class of `x`, over any family of representatives of the right
cosets.** If the right cosets `Γ₁' aᵢ` are pairwise distinct and cover `Γ₁' D.out Γ₂'`, and each
`aᵢ` is the cast of the integral matrix `Aᵢ`, then `T_D [x] = ∑ᵢ [aᵢ · x]`. -/
theorem heckeSymbol_mk_eq_sum_of_rightCosets {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ)
    (ha : ∀ i, a i ∈ intEntries 2)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) =
      ⋃ i, op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D hD (Coinvariants.mk _ x) =
      ∑ i, (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w) (symbolIntRep R w ⟨a i, ha i⟩ x) := by
  rw [heckeSymbol_mk_eq_heckeSum, HeckeCoset.heckeSum_eq_sum_of_rightCosets D
    (symbolIntRep R w) hD (map_mapGL_le_intEntries 2 Γ₂) (map_mapGL_le_intEntries 2 Γ₁)
    (fun _ hγ ↦ mk_comp_symbolIntRep_of_mem Γ₁ hγ) a ha hcover hinj, LinearMap.sum_apply]
  rfl

/-- **The Hecke operator on a modular symbol, over any family of representatives of the right
cosets.** If the right cosets `Γ₁' aᵢ` are pairwise distinct and cover `Γ₁' D.out Γ₂'`, and
`aᵢ` is the cast of the integral matrix `Aᵢ`, then
`T_D ({α, β} ⊗ P) = ∑ᵢ {aᵢα, aᵢβ} ⊗ (P ∣ adj Aᵢ)`. This is the form in which explicit coset
representatives — say the matrices `!![1, j; 0, p]` and `!![p, 0; 0, 1]` for `T_p` — are read
off. -/
theorem heckeSymbol_symbol_eq_sum_of_rightCosets {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ)
    (A : ι → Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ i, (a i : Matrix (Fin 2) (Fin 2) ℚ) = (A i).map (Int.cast : ℤ → ℚ))
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) =
      ⋃ i, op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (α β : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D hD (symbol Γ₂ α β P) =
      ∑ i, symbol Γ₁ (a i • α) (a i • β) (binaryFormRep R w (op (adjugate (A i))) P) := by
  have ha : ∀ i, a i ∈ intEntries 2 := fun i ↦
    (mem_intEntries 2).mpr ((hasIntEntries_iff 2).mpr ⟨A i, hA i⟩)
  rw [symbol_apply, heckeSymbol_mk_eq_sum_of_rightCosets Γ₁ Γ₂ D hD a ha hcover hinj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mk_symbolIntRep_tmul Γ₁ ⟨a i, ha i⟩ α β P, (intMatrix_eq_iff 2).mpr (hA i)]

/-- **The identity double coset acts as the identity** on `𝕄_w(Γ; R)`: `Γ' · 1 · Γ' = Γ'` is a
single right coset, represented by `1`. -/
@[simp]
theorem heckeSymbol_one (Γ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
    (hD : ((1 : HeckeCoset Δ (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ))).out : GL (Fin 2) ℚ) ∈
      intEntries 2)
    [Finite (DecompQuotient (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ))
      ((1 : HeckeCoset Δ (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ))).out : GL (Fin 2) ℚ)⁻¹)] :
    heckeSymbol Γ Γ (1 : HeckeCoset Δ (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ))) hD =
      (LinearMap.id : ModularSymbols R Γ w →ₗ[R] ModularSymbols R Γ w) := by
  refine Coinvariants.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hcover : doubleCoset ((1 : HeckeCoset Δ (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ))).out :
      GL (Fin 2) ℚ) (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ)) =
      ⋃ _ : Unit, op (1 : GL (Fin 2) ℚ) • (Γ.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
    rw [Set.iUnion_const, op_one, one_smul, ← HeckeCoset.rep_def,
      ← HeckeCoset.toSet_eq_doubleCoset_rep, HeckeCoset.toSet_one]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
    heckeSymbol_mk_eq_sum_of_rightCosets Γ Γ _ hD _ (fun _ ↦ one_mem _) hcover
      (Function.injective_of_subsingleton _), Fintype.sum_unique]
  congr 1
  exact congrArg (fun e ↦ e x) (map_one (symbolIntRep R w))

/-! ### The Hecke operators `T_n` at level `Γ₁(N)` -/

variable (N : ℕ) [NeZero N]

variable (R w) in
/-- **The Hecke operator `T_n` on `𝕄_w(Γ₁(N); R)`**: the operator of the double coset
`Γ₁(N) · diag(1, n) · Γ₁(N)`, the same double coset that defines `T_n` on modular forms of level
`Γ₁(N)` (`HeckeRing.GL2.heckeTNat`). The `NeZero n` binder records that Hecke operators are indexed
by positive integers; at `n = 0` the double coset would degenerate to `Γ₁(N)` itself. As for
`heckeTNat`, the binder is `_`-named because only the *statements* use it: the body is the same
operator either way, and it is the index that is being constrained. -/
noncomputable def heckeTSymbol (n : ℕ) [_hn : NeZero n] :
    Module.End R (ModularSymbols R (Gamma1 N) w) :=
  heckeSymbol (Gamma1 N) (Gamma1 N) (diagCosetGamma1 N n)
    (Delta0_le_intEntries N (diagCosetGamma1 N n).out.2)

/-- The defining equation of `heckeTSymbol`. -/
theorem heckeTSymbol_def (n : ℕ) [NeZero n] :
    heckeTSymbol R w N n =
      heckeSymbol (Gamma1 N) (Gamma1 N) (diagCosetGamma1 N n)
        (Delta0_le_intEntries N (diagCosetGamma1 N n).out.2) := (rfl)

/-- **Transport `T_n` along an equality of indices.** -/
theorem heckeTSymbol_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    heckeTSymbol R w N n = heckeTSymbol R w N m := by
  subst h
  rfl

/-- The first Hecke operator on modular symbols is the identity. -/
@[simp]
theorem heckeTSymbol_one : heckeTSymbol R w N 1 = 1 := by
  have h : diagCosetGamma1 N 1 = 1 := by
    rw [diagCosetGamma1_def, HeckeCoset.one_def]
    refine congrArg (HeckeCoset.mk _ _) (Subtype.ext ?_)
    exact (congrArg (natDiagGL 2) (funext fun i ↦ by fin_cases i <;> rfl)).trans
      (natDiagGL_one 2)
  rw [heckeTSymbol_def, h, heckeSymbol_one]
  rfl

end TauCeti.ModularSymbols

end
