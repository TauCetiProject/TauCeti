/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Centralizers of character kernels of a split maximal torus

Let `T = D(X)` be a chosen split maximal torus of an affine group `G = Spec H` over a commutative
ring `R`, with character lattice `X = ℤ^r` written additively, and let `α ∈ X`. This file
attaches to `α` the two subgroups of `G` from which the rank-one structure along a root `α` is
built.

* The kernel `ker α` of the character is the diagonalizable subgroup `D(X ⧸ ℤα)` of `T`. Its
  centralizer `Z_G(ker α)` is `SplitMaximalTorus.centralizerKerHopfIdeal`.
* The characters of `ker α` modulo torsion form the lattice `(X ⧸ ℤα) ⧸ torsion`, which is free.
  The corresponding subgroup `T_α = D((X ⧸ ℤα) ⧸ torsion)` of `ker α` is therefore a split torus
  (`SplitMaximalTorus.splitTorus_kerTorus`). Over a field, `T_α` is classically
  `((ker α)°)_red`: the quotient `ker α ⧸ T_α` is the finite diagonalizable group whose character
  group is the torsion of `X ⧸ ℤα`. In characteristic zero this is `(ker α)°`, but in
  characteristic `p` the identity component can be larger: for `T = 𝔾ₘ` and `α = p`, `ker α = μₚ`
  is connected while `T_α` is trivial. These identifications are not proved here. The centralizer
  `Z_G(T_α)` is `SplitMaximalTorus.centralizerKerTorusHopfIdeal`.

A character `χ` vanishes on `T_α` exactly when some positive multiple of `χ` lies in `ℤα`
(`SplitMaximalTorus.ofAdd_mem_ker_kerTorusCharacterMap_iff`), so `T_α` is cut out by the
characters lying on the rational line through `α`.

Both centralizers contain `T`, and the inclusions `T_α ⊆ ker α ⊆ T` give
`Z_G(T) ⊆ Z_G(ker α) ⊆ Z_G(T_α)`. Their Lie algebras are read off from the weight decomposition
`𝔤 = ⨁ χ, 𝔤_χ` of `Lie G` under `T`:

`Lie Z_G(ker α) = ⨆ n : ℤ, 𝔤_{nα}`, `Lie Z_G(T_α) = ⨆ {χ | ∃ n > 0, n • χ ∈ ℤα}, 𝔤_χ`.

Classically, when `G` is connected reductive over an algebraically closed field and `α` is a root,
`Z_G(T_α)` is the connected reductive subgroup of semisimple rank one inside which the root group
`U_α` and the coroot of `α` are constructed; that theory is not developed here.
Nothing here assumes a field, smoothness, reductivity, or that `α` is a root; the Lie-algebra
statements assume only that the augmentation cotangent module of `H` is finite projective.

## Main declarations

* `TauCeti.SplitMaximalTorus.kerCoordinateMap`, `TauCeti.SplitMaximalTorus.kerTorusCoordinateMap`:
  the closed immersions `ker α → G` and `T_α → G`, in coordinates.
* `TauCeti.SplitMaximalTorus.splitTorus_kerTorus`: `T_α` is a split torus.
* `TauCeti.SplitMaximalTorus.centralizerKerHopfIdeal`: the centralizer `Z_G(ker α)`.
* `TauCeti.SplitMaximalTorus.centralizerKerTorusHopfIdeal`: the centralizer `Z_G(T_α)`.
* `TauCeti.SplitMaximalTorus.centralizerKerHopfIdeal_le_definingIdeal`,
  `TauCeti.SplitMaximalTorus.centralizerKerHopfIdeal_le_centralizerHopfIdeal` and
  `TauCeti.SplitMaximalTorus.centralizerKerTorusHopfIdeal_le_centralizerKerHopfIdeal`: the
  containments `T ⊆ Z_G(ker α)` and `Z_G(T) ⊆ Z_G(ker α) ⊆ Z_G(T_α)`.
* `TauCeti.SplitMaximalTorus.lieSubalgebra_centralizerKerHopfIdeal_toSubmodule` and
  `TauCeti.SplitMaximalTorus.lieSubalgebra_centralizerKerTorusHopfIdeal_toSubmodule`: their Lie
  algebras.

## References

* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §7.1.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §13.18.
-/

public section

open CategoryTheory

namespace TauCeti.SplitMaximalTorus

universe u

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}

/-! ### The kernel of a character and its torus -/

/-- The character group of `ker α`: the characters of the split torus modulo `ℤα`. -/
abbrev KerCharacterGroup (α : ULift.{u} (Fin r) →₀ ℤ) : Type u :=
  Multiplicative (ULift.{u} (Fin r) →₀ ℤ) ⧸ Subgroup.zpowers (Multiplicative.ofAdd α)

/-- The character group of the torus `T_α`: the characters of `ker α` modulo torsion. -/
abbrev KerTorusCharacterGroup (α : ULift.{u} (Fin r) →₀ ℤ) : Type u :=
  KerCharacterGroup α ⧸ CommGroup.torsion (KerCharacterGroup α)

/-- Restriction of characters from the split torus to the torus `T_α`. -/
noncomputable def kerTorusCharacterMap (α : ULift.{u} (Fin r) →₀ ℤ) :
    Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* KerTorusCharacterGroup α :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

/-- Restriction to `T_α` sends a character to its class modulo `ℤα` and torsion. -/
theorem kerTorusCharacterMap_apply (α : ULift.{u} (Fin r) →₀ ℤ)
    (χ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) :
    kerTorusCharacterMap α χ = ((χ : KerCharacterGroup α) : KerTorusCharacterGroup α) :=
  (rfl)

/-- The restriction map to the characters of `T_α` is surjective. -/
theorem kerTorusCharacterMap_surjective (α : ULift.{u} (Fin r) →₀ ℤ) :
    Function.Surjective (kerTorusCharacterMap α) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

/-- **A character vanishes on `T_α` exactly when a positive multiple of it lies in `ℤα`.** -/
theorem ofAdd_mem_ker_kerTorusCharacterMap_iff (α χ : ULift.{u} (Fin r) →₀ ℤ) :
    Multiplicative.ofAdd χ ∈ (kerTorusCharacterMap α).ker ↔
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, n • χ = m • α := by
  rw [MonoidHom.mem_ker, kerTorusCharacterMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Subgroup.mem_zpowers_iff]
  refine exists_congr fun m ↦ ?_
  rw [← ofAdd_zsmul, ← ofAdd_nsmul, EmbeddingLike.apply_eq_iff_eq, eq_comm]

/-- The characters of `T_α` form a finitely generated torsion-free group. -/
noncomputable abbrev kerTorusCharacterFGGroup (α : ULift.{u} (Fin r) →₀ ℤ) : FGCommGrpCat.{u} :=
  FGCommGrpCat.of (KerTorusCharacterGroup α)

/-- **`T_α` is a split torus**: its character group is finitely generated and torsion-free, hence
free. -/
theorem splitTorus_kerTorus (α : ULift.{u} (Fin r) →₀ ℤ) :
    splitTorusCommHopfAlgProperty R
      (DiagonalizableGroup.coordinateRing R (kerTorusCharacterFGGroup α)) :=
  splitTorusCommHopfAlgProperty_coordinateRing R (kerTorusCharacterFGGroup α)

/-- Restriction of functions on `G` to `ker α`, the composite of restriction to `T` and
restriction of characters to `ker α`. -/
noncomputable def kerCoordinateMap (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    H →ₐc[R] MonoidAlgebra R (KerCharacterGroup α) :=
  (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' _)).comp T.coordinateMap.hom

/-- Restriction to `ker α` is restriction to `T` followed by passing to classes modulo `ℤα`. -/
theorem kerCoordinateMap_def (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.kerCoordinateMap α =
      (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' _)).comp T.coordinateMap.hom :=
  (rfl)

/-- Restriction of functions on `G` to `T_α`. -/
noncomputable def kerTorusCoordinateMap (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : H →ₐc[R] MonoidAlgebra R (KerTorusCharacterGroup α) :=
  (MonoidAlgebra.mapDomainBialgHom R (kerTorusCharacterMap α)).comp T.coordinateMap.hom

/-- Restriction to `T_α` is restriction to `T` followed by restriction of characters. -/
theorem kerTorusCoordinateMap_def (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.kerTorusCoordinateMap α =
      (MonoidAlgebra.mapDomainBialgHom R (kerTorusCharacterMap α)).comp T.coordinateMap.hom :=
  (rfl)

/-- `T_α → G` factors through `ker α → G`: restriction to `T_α` is restriction to `ker α` followed
by restriction of characters modulo torsion. -/
theorem kerTorusCoordinateMap_eq_comp (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.kerTorusCoordinateMap α =
      (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' _)).comp (T.kerCoordinateMap α) := by
  rw [kerTorusCoordinateMap, kerCoordinateMap, kerTorusCharacterMap,
    MonoidAlgebra.mapDomainBialgHom_comp, BialgHom.comp_assoc]

/-- `ker α` is a closed subgroup of `G`. -/
theorem kerCoordinateMap_surjective (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : Function.Surjective (T.kerCoordinateMap α) :=
  (MonoidAlgebra.mapDomain_surjective (QuotientGroup.mk'_surjective _)).comp T.surjective

/-- `T_α` is a closed subgroup of `G`. -/
theorem kerTorusCoordinateMap_surjective (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : Function.Surjective (T.kerTorusCoordinateMap α) :=
  (MonoidAlgebra.mapDomain_surjective (kerTorusCharacterMap_surjective α)).comp T.surjective

/-! ### The two centralizers -/

/-- **The centralizer `Z_G(ker α)` of the kernel of a character** of a split maximal torus. -/
noncomputable def centralizerKerHopfIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : HopfIdeal R H :=
  BialgHom.centralizerHopfIdeal (T.kerCoordinateMap α)

/-- `Z_G(ker α)` is the centralizer of the diagonalizable subgroup `ker α → G`. -/
theorem centralizerKerHopfIdeal_def (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerHopfIdeal α = BialgHom.centralizerHopfIdeal (T.kerCoordinateMap α) :=
  (rfl)

/-- **The centralizer `Z_G(T_α)` of the torus of the kernel of a character** of a split maximal
torus. -/
noncomputable def centralizerKerTorusHopfIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : HopfIdeal R H :=
  BialgHom.centralizerHopfIdeal (T.kerTorusCoordinateMap α)

/-- `Z_G(T_α)` is the centralizer of the diagonalizable subgroup `T_α → G`. -/
theorem centralizerKerTorusHopfIdeal_def (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerTorusHopfIdeal α = BialgHom.centralizerHopfIdeal (T.kerTorusCoordinateMap α) :=
  (rfl)

/-- **`Z_G(T) ⊆ Z_G(ker α)`**: a point centralizing the torus centralizes the kernel of each of its
characters. -/
theorem centralizerKerHopfIdeal_le_centralizerHopfIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerHopfIdeal α ≤ BialgHom.centralizerHopfIdeal T.coordinateMap.hom := by
  rw [centralizerKerHopfIdeal_def, kerCoordinateMap_def]
  exact BialgHom.centralizerHopfIdeal_comp_le _ _

/-- **`T ⊆ Z_G(ker α)`**: the torus centralizes the kernel of each of its characters. -/
theorem centralizerKerHopfIdeal_le_definingIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : T.centralizerKerHopfIdeal α ≤ T.definingIdeal := by
  intro x hx
  rw [centralizerKerHopfIdeal_def, kerCoordinateMap_def] at hx
  exact (T.mem_definingIdeal x).2 <| (HopfIdeal.mem_kerOfSurjective _ T.surjective).1 <|
    BialgHom.centralizerHopfIdeal_comp_le_kerOfSurjective _ T.surjective _ hx

/-- **`Z_G(ker α) ⊆ Z_G(T_α)`**, since `T_α ⊆ ker α`. -/
theorem centralizerKerTorusHopfIdeal_le_centralizerKerHopfIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerTorusHopfIdeal α ≤ T.centralizerKerHopfIdeal α := by
  rw [centralizerKerTorusHopfIdeal_def, kerTorusCoordinateMap_eq_comp, centralizerKerHopfIdeal_def]
  exact BialgHom.centralizerHopfIdeal_comp_le _ _

/-- **`T ⊆ Z_G(T_α)`**. -/
theorem centralizerKerTorusHopfIdeal_le_definingIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) : T.centralizerKerTorusHopfIdeal α ≤ T.definingIdeal :=
  (T.centralizerKerTorusHopfIdeal_le_centralizerKerHopfIdeal α).trans
    (T.centralizerKerHopfIdeal_le_definingIdeal α)

private noncomputable def kerCharacterZeroLift (r : ℕ) :
    KerCharacterGroup (0 : ULift.{u} (Fin r) →₀ ℤ) →*
      Multiplicative (ULift.{u} (Fin r) →₀ ℤ) :=
  QuotientGroup.lift _ (MonoidHom.id _) (by simp)

omit [Algebra.FiniteType R H] in
private theorem centralizerHopfIdeal_mapDomain_comp_eq_of_comp_eq_id
    {Γ Δ : Type u} [CommGroup Γ] [CommGroup Δ]
    (φ : H →ₐc[R] MonoidAlgebra R Γ) (f : Γ →* Δ) (g : Δ →* Γ)
    (hgf : g.comp f = MonoidHom.id Γ) :
    BialgHom.centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R f).comp φ) =
      BialgHom.centralizerHopfIdeal φ := by
  refine le_antisymm (BialgHom.centralizerHopfIdeal_comp_le _ _) ?_
  have hπ : (MonoidAlgebra.mapDomainBialgHom R g).comp
      ((MonoidAlgebra.mapDomainBialgHom R f).comp φ) = φ := by
    rw [← BialgHom.comp_assoc, ← MonoidAlgebra.mapDomainBialgHom_comp, hgf,
      MonoidAlgebra.mapDomainBialgHom_id]
    exact BialgHom.id_comp _
  calc
    BialgHom.centralizerHopfIdeal φ = BialgHom.centralizerHopfIdeal
        ((MonoidAlgebra.mapDomainBialgHom R g).comp
          ((MonoidAlgebra.mapDomainBialgHom R f).comp φ)) :=
      congrArg BialgHom.centralizerHopfIdeal hπ.symm
    _ ≤ _ := BialgHom.centralizerHopfIdeal_comp_le _ _

/-- The kernel of the zero character is the whole torus, so `Z_G(ker 0) = Z_G(T)`. -/
@[simp]
theorem centralizerKerHopfIdeal_zero (T : SplitMaximalTorus R H r) :
    T.centralizerKerHopfIdeal 0 = BialgHom.centralizerHopfIdeal T.coordinateMap.hom := by
  rw [centralizerKerHopfIdeal_def, kerCoordinateMap]
  exact centralizerHopfIdeal_mapDomain_comp_eq_of_comp_eq_id T.coordinateMap.hom
    (QuotientGroup.mk' _) (kerCharacterZeroLift r) (QuotientGroup.lift_comp_mk' _ _ _)

/-- The torus of the kernel of the zero character is the whole torus, so `Z_G(T_0) = Z_G(T)`. -/
@[simp]
theorem centralizerKerTorusHopfIdeal_zero (T : SplitMaximalTorus R H r) :
    T.centralizerKerTorusHopfIdeal 0 = BialgHom.centralizerHopfIdeal T.coordinateMap.hom := by
  -- Restriction has a left inverse: the character lattice has no nontrivial torsion.
  let f := kerCharacterZeroLift r
  let g : KerTorusCharacterGroup (0 : ULift.{u} (Fin r) →₀ ℤ) →*
      Multiplicative (ULift.{u} (Fin r) →₀ ℤ) :=
    QuotientGroup.lift _ f (by
      intro χ hχ
      have ht : f χ ∈ CommGroup.torsion (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) :=
        CommGroup.le_comap_torsion f hχ
      have htor : CommGroup.torsion (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) = ⊥ :=
        CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp inferInstance
      simpa only [htor, Subgroup.mem_bot, MonoidHom.mem_ker] using ht)
  have hf : f.comp (QuotientGroup.mk' _) = MonoidHom.id _ :=
    QuotientGroup.lift_comp_mk' _ _ _
  have hg : g.comp (QuotientGroup.mk' _) = f := QuotientGroup.lift_comp_mk' _ _ _
  have hgf : g.comp (kerTorusCharacterMap 0) = MonoidHom.id _ := by
    rw [kerTorusCharacterMap, ← MonoidHom.comp_assoc, hg, hf]
  rw [centralizerKerTorusHopfIdeal_def, kerTorusCoordinateMap]
  exact centralizerHopfIdeal_mapDomain_comp_eq_of_comp_eq_id T.coordinateMap.hom
    (kerTorusCharacterMap 0) g hgf

/-- The kernel of `-α` is the kernel of `α`, so `Z_G(ker (-α)) = Z_G(ker α)`. -/
@[simp]
theorem centralizerKerHopfIdeal_neg (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerHopfIdeal (-α) = T.centralizerKerHopfIdeal α := by
  have h : Subgroup.zpowers (Multiplicative.ofAdd (-α)) =
      Subgroup.zpowers (Multiplicative.ofAdd α) := by
    rw [ofAdd_neg, Subgroup.zpowers_inv]
  rw [centralizerKerHopfIdeal_def, centralizerKerHopfIdeal_def, kerCoordinateMap_def,
    kerCoordinateMap_def]
  exact le_antisymm
    (BialgHom.centralizerHopfIdeal_mapDomainBialgHom_mk'_comp_anti _ h.ge)
    (BialgHom.centralizerHopfIdeal_mapDomainBialgHom_mk'_comp_anti _ h.le)

/-- The torus of the kernel of `-α` is that of `α`, so `Z_G(T_{-α}) = Z_G(T_α)`. -/
@[simp]
theorem centralizerKerTorusHopfIdeal_neg (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.centralizerKerTorusHopfIdeal (-α) = T.centralizerKerTorusHopfIdeal α := by
  -- Restriction of characters to `T_{-β}` factors through restriction to `T_β`.
  have key (β : ULift.{u} (Fin r) →₀ ℤ) :
      T.centralizerKerTorusHopfIdeal (-β) ≤ T.centralizerKerTorusHopfIdeal β := by
    have h : Subgroup.zpowers (Multiplicative.ofAdd β) ≤
        Subgroup.zpowers (Multiplicative.ofAdd (-β)) := by
      rw [ofAdd_neg, Subgroup.zpowers_inv]
    let f : KerCharacterGroup β →* KerCharacterGroup (-β) :=
      QuotientGroup.map _ _ (MonoidHom.id _) h
    let g : KerTorusCharacterGroup β →* KerTorusCharacterGroup (-β) :=
      QuotientGroup.map _ _ f (CommGroup.le_comap_torsion f)
    have hg : g.comp (kerTorusCharacterMap β) = kerTorusCharacterMap (-β) := by
      ext
      rfl
    rw [centralizerKerTorusHopfIdeal_def, centralizerKerTorusHopfIdeal_def,
      kerTorusCoordinateMap_def, kerTorusCoordinateMap_def, ← hg,
      MonoidAlgebra.mapDomainBialgHom_comp, BialgHom.comp_assoc]
    exact BialgHom.centralizerHopfIdeal_comp_le _ _
  exact le_antisymm (key α) (by simpa using key (-α))

/-! ### Lie algebras -/

section Lie

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- A tangent vector lies in the Lie algebra of `Z_G(ker α)` exactly when it is a sum of weight
vectors of `T` whose weights are multiples of `α`. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_centralizerKerHopfIdeal_iff
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.cotangentLinearEquiv (B := R) x ∈
        (T.centralizerKerHopfIdeal α).lieSubalgebra (B := R) ↔
      x ∈ ⨆ n : ℤ, Derivation.adjointWeightSpace T.coordinateMap.hom
        (Multiplicative.ofAdd (n • α)) := by
  rw [centralizerKerHopfIdeal, kerCoordinateMap,
    BialgHom.cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_mapDomainBialgHom_comp_iff,
    QuotientGroup.ker_mk']
  simp only [Subgroup.mem_zpowers_iff, iSup_exists]
  rw [iSup_comm]
  simp only [iSup_iSup_eq_right, ← ofAdd_zsmul]
  -- The sides differ only in the carrier `SplitTorus.characterGroup`, which unfolds to
  -- `Multiplicative (ULift (Fin r) →₀ ℤ)` by definition.
  exact Iff.rfl

/-- **The Lie algebra of `Z_G(ker α)` is `⨆ n : ℤ, 𝔤_{nα}`**, the sum of the weight spaces of `T`
on the multiples of `α`, transported along cotangent duality. -/
theorem lieSubalgebra_centralizerKerHopfIdeal_toSubmodule (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    ((T.centralizerKerHopfIdeal α).lieSubalgebra (B := R)).toSubmodule =
      (⨆ n : ℤ, Derivation.adjointWeightSpace T.coordinateMap.hom
          (Multiplicative.ofAdd (n • α))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_map_equiv,
    ← cotangentLinearEquiv_mem_lieSubalgebra_centralizerKerHopfIdeal_iff,
    LinearEquiv.apply_symm_apply]

/-- A tangent vector lies in the Lie algebra of `Z_G(T_α)` exactly when it is a sum of weight
vectors of `T` whose weights have a positive multiple in `ℤα`. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_centralizerKerTorusHopfIdeal_iff
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.cotangentLinearEquiv (B := R) x ∈
        (T.centralizerKerTorusHopfIdeal α).lieSubalgebra (B := R) ↔
      x ∈ ⨆ (χ : ULift.{u} (Fin r) →₀ ℤ) (_ : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, n • χ = m • α),
        Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd χ) := by
  rw [centralizerKerTorusHopfIdeal, kerTorusCoordinateMap,
    BialgHom.cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_mapDomainBialgHom_comp_iff]
  rw [← Multiplicative.ofAdd.iSup_comp]
  simp only [ofAdd_mem_ker_kerTorusCharacterMap_iff]
  -- The sides differ only in the carrier `SplitTorus.characterGroup`, which unfolds to
  -- `Multiplicative (ULift (Fin r) →₀ ℤ)` by definition.
  exact Iff.rfl

/-- **The Lie algebra of `Z_G(T_α)`** is the sum of the weight spaces `𝔤_χ` of `T` over the
characters `χ` with a positive multiple in `ℤα`, transported along cotangent duality. -/
theorem lieSubalgebra_centralizerKerTorusHopfIdeal_toSubmodule (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    ((T.centralizerKerTorusHopfIdeal α).lieSubalgebra (B := R)).toSubmodule =
      (⨆ (χ : ULift.{u} (Fin r) →₀ ℤ) (_ : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, n • χ = m • α),
          Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd χ)).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_map_equiv,
    ← cotangentLinearEquiv_mem_lieSubalgebra_centralizerKerTorusHopfIdeal_iff,
    LinearEquiv.apply_symm_apply]

end Lie

end TauCeti.SplitMaximalTorus
