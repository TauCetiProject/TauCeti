/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.Lie.Sl2.Classification
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.FiniteEtale
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
import TauCeti.Algebra.AlgebraicGroup.Representation.Integration
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.Tangent.Etale
import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.Coalgebra.Subcomodule.Finrank
import TauCeti.Algebra.Lie.Sl2.CompleteReducibility
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Integrating `sl₂`-representations and Lie homomorphisms to `SL₂`

Over an algebraically closed field `k` of characteristic zero, the special linear group `SL₂` is
simply connected: every finite-dimensional representation of `sl(2, k)` integrates to a unique
rational representation of `SL₂`, and every Lie algebra homomorphism `sl(2, k) → Lie(G)` into the
tangent Lie algebra of a finite-type affine group `G` integrates to a unique algebraic group
homomorphism `SL₂ → G`.

Both statements are proved without universal enveloping algebras or exponential power series:

1. **Irreducible representations.** The degree-`d` binary forms `binaryForms k d` form a simple
   `SL₂`-comodule of dimension `d + 1` in characteristic zero. Because `SL₂` is connected and
   smooth, `sl(2, k)`-stable subspaces of `binaryForms k d` are subcomodules
   (`Submodule.exists_subcomodule_iff_forall_differential_mem`), so `binaryForms k d` is an
   irreducible `sl(2, k)`-module of dimension `d + 1`, hence isomorphic to `Sl2Std k d` by the
   highest-weight classification (`TauCeti.Sl2Std.existsUnique_nonempty_lieModuleEquiv`).
2. **All finite-dimensional representations.** Complete reducibility of finite-dimensional
   `sl(2, k)`-modules (`TauCeti.exists_isCompl_sl_fin_two`) decomposes any finite-dimensional
   `sl(2, k)`-module into irreducibles by strong induction on dimension, transporting direct-sum
   and binary-form coactions across linear equivalences via
   `TauCeti.Comodule.differential_prod` and `TauCeti.Comodule.differential_transport`. Uniqueness
   of the integrating comodule follows from `TauCeti.Comodule.ext_of_differential_eq`.
3. **Homomorphisms into a finite-type affine group.** Given `φ : sl(2, k) →ₗ⁅k⁆ Lie(G)`, choose a
   faithful finite-dimensional `G`-comodule `M` with basis `b` so that the coordinate morphism
   `π : O(GLₙ) → O(G)` is surjective (`TauCeti.Comodule.exists_coordinateBialgHom_surjective`).
   Restricting the differentiated `G`-action on `M` along `φ` makes `M` an `sl(2, k)`-module, which
   integrates to an `SL₂`-comodule and descends uniquely to `O(G) → O(SL₂)` with differential `φ`
   by `TauCeti.CommHopfAlgCat.existsUnique_bialgHom_derivationCompLieHom_eq_of_surjective`.
4. **Centrality of the kernel.** When `φ` is injective, the scheme-theoretic kernel of `SL₂ → G`
   has zero Lie algebra, hence trivial identity component, so it is finite, smooth, and normal in
   the connected group `SL₂`, hence central (`IsNormal.isCentral_of_finite_of_isReduced`), i.e.
   contained in `Z(SL₂) = μ₂ = {±I}`.

No connectedness or reducedness assumption is needed on the target group `G`.

## Main declarations

* `TauCeti.SpecialLinear.slDifferential`, `TauCeti.SpecialLinear.slLieRingModule`, and
  `TauCeti.SpecialLinear.slLieModule`: the differentiated `slₙ`-module structure on an
  `O(SLₙ)`-comodule.
* `TauCeti.SpecialLinear.finrank_binaryForms` and
  `TauCeti.SpecialLinear.nonempty_lieModuleEquiv_binaryForms_sl2Std`: `dim_R (binaryForms R d) =
  d + 1`, and over an algebraically closed field of characteristic zero `binaryForms k d` is
  isomorphic as an `sl(2, k)`-module to `Sl2Std k d`.
* `TauCeti.SpecialLinear.existsUnique_comodule_of_lieModule`: every finite-dimensional
  `sl(2, k)`-module integrates to a unique `SL₂`-comodule.
* `TauCeti.SpecialLinear.integrateLieHom`: the unique bialgebra morphism
  `H →ₐc[k] coordinateHopfAlgebra k 2` integrating `φ : sl(2, k) →ₗ⁅k⁆ Lie(Spec H)`, with
  differential computation rules `derivationComp_integrateLieHom`,
  `derivationCompLieHom_integrateLieHom`, uniqueness `eq_integrateLieHom_iff`, functoriality
  `integrateLieHom_comp`, and central `{±I}` kernel theorems
  `isCentral_kernelHopfIdeal_integrateLieHom`,
  `centerDefiningIdeal_le_kernelHopfIdeal_integrateLieHom`, and
  `pointsMulEquiv_eq_one_or_neg_one_of_mem_kernel_integrateLieHom`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §31.1 and §32.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.2–§3.4.
-/

public section

open CategoryTheory Module WithConv

namespace TauCeti

universe u v w

/-! ### Integrating `sl₂`-representations via binary forms and complete reducibility -/

namespace SpecialLinear

section BinaryFormFinrank

variable (R : Type u) [CommRing R] [StrongRankCondition R]

/-- The binary forms of degree `d` over a commutative ring satisfying the strong rank condition
have rank `d + 1`. -/
@[simp]
theorem finrank_binaryForms (d : ℕ) :
    letI := polynomialComodule R 2
    Module.finrank R (binaryForms R d) = d + 1 := by
  let _ := polynomialComodule R 2
  have hsub : (binaryForms R d).toSubmodule = MvPolynomial.homogeneousSubmodule (Fin 2) R d := by
    ext f
    exact mem_binaryForms
  rw [← Subcomodule.finrank_toSubmodule, hsub]
  exact TauCeti.finrank_homogeneousSubmodule_fin_two R d

end BinaryFormFinrank

section SlDifferential

variable {R : Type u} [CommRing R] (n : ℕ)
variable {M : Type w} [AddCommGroup M] [Module R M] [Comodule R (coordinateHopfAlgebra R n) M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The differentiated `slₙ`-representation associated to a comodule over `O(SLₙ)`. -/
noncomputable def slDifferential :
    LieAlgebra.SpecialLinear.sl (Fin n) R →ₗ⁅R⁆ Module.End R M :=
  (Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) (M := M)).comp
    (tangentLieEquivSl (R := R) (B := R) n).symm.toLieHom

@[simp]
theorem slDifferential_apply (X : LieAlgebra.SpecialLinear.sl (Fin n) R) (m : M) :
    slDifferential n X m =
      Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) (M := M)
        ((tangentLieEquivSl (R := R) (B := R) n).symm X) m :=
  (rfl)

theorem slDifferential_tangentLieEquivSl
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) R)) (m : M) :
    slDifferential n (tangentLieEquivSl n d) m =
      Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) (M := M) d m := by
  rw [slDifferential_apply, LieEquiv.symm_apply_apply]

/-- The `LieRingModule` structure on an `O(SLₙ)`-comodule induced by `slDifferential`. -/
@[instance_reducible]
noncomputable def slLieRingModule (R : Type u) [CommRing R] (n : ℕ)
    (M : Type w) [AddCommGroup M] [Module R M] [Comodule R (coordinateHopfAlgebra R n) M] :
    LieRingModule (LieAlgebra.SpecialLinear.sl (Fin n) R) M :=
  LieRingModule.compLieHom M (slDifferential (R := R) (M := M) n)

attribute [local instance] slLieRingModule

/-- The `LieModule` structure on an `O(SLₙ)`-comodule induced by `slDifferential`. -/
theorem slLieModule (R : Type u) [CommRing R] (n : ℕ)
    (M : Type w) [AddCommGroup M] [Module R M] [Comodule R (coordinateHopfAlgebra R n) M] :
    LieModule R (LieAlgebra.SpecialLinear.sl (Fin n) R) M :=
  LieModule.compLieHom M (slDifferential (R := R) (M := M) n)

@[simp]
theorem slLieRingModule_bracket (X : LieAlgebra.SpecialLinear.sl (Fin n) R) (m : M) :
    ⁅X, m⁆ = slDifferential n X m :=
  (rfl)

end SlDifferential

section AlgClosedCharZero

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

private instance instConnectedSpaceOfCoordinateHopfAlgebra (n : ℕ) :
    ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n))) :=
  (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n).connectedSpace k
    (_root_.CommHopfAlgCat.of k (coordinateHopfAlgebra k n))

/-- Over an algebraically closed field of characteristic zero, any `slₙ`-stable subspace of an
`SLₙ`-comodule comes from a subcomodule. -/
theorem exists_subcomodule_of_slDifferential_mem (n : ℕ)
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k (coordinateHopfAlgebra k n) M]
    (W : Submodule k M)
    (hW : ∀ X : LieAlgebra.SpecialLinear.sl (Fin n) k, ∀ w ∈ W,
      slDifferential (M := M) n X w ∈ W) :
    ∃ N : Subcomodule k (coordinateHopfAlgebra k n) M, N.toSubmodule = W := by
  refine (Submodule.exists_subcomodule_iff_forall_differential_mem
    (H := FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) W).mpr fun δ w hw ↦ ?_
  rw [← slDifferential_tangentLieEquivSl]
  exact hW (tangentLieEquivSl (R := k) (B := k) n δ) w hw

section BinaryFormsIrreducible

attribute [local instance] polynomialComodule slLieRingModule slLieModule
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem eq_bot_or_eq_top_of_differential_mem_binaryForms (d : ℕ)
    (S : Submodule k (binaryForms k d))
    (hS : ∀ δ : Derivation k (coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k), ∀ w ∈ S,
      Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2)
        (M := binaryForms k d) δ w ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  obtain ⟨N, hN⟩ := (Submodule.exists_subcomodule_iff_forall_differential_mem
    (H := FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k 2)) S).mpr hS
  let M : Subcomodule k (coordinateHopfAlgebra k 2) (MvPolynomial (Fin 2) k) :=
    N.map (binaryForms k d).subtype
  have hMle : M ≤ binaryForms k d := by
    rw [← Subcomodule.toSubmodule_le_toSubmodule, Subcomodule.map_toSubmodule]
    rintro _ ⟨w, -, rfl⟩
    rw [Subcomodule.subtype_toLinearMap, SMulMemClass.subtype_apply, Subcomodule.mem_toSubmodule]
    exact w.2
  rcases (isAtom_binaryForms_of_charZero (k := k) (d := d)).le_iff.mp hMle with hbot | htop
  · left
    rw [eq_bot_iff, ← hN]
    intro x hx
    have hx' : (binaryForms k d).subtype.toLinearMap x ∈ M.toSubmodule := by
      rw [Subcomodule.map_toSubmodule]
      exact Submodule.mem_map_of_mem hx
    rw [hbot, Subcomodule.bot_toSubmodule, Submodule.mem_bot,
      Subcomodule.subtype_toLinearMap, SMulMemClass.subtype_apply] at hx'
    exact Subtype.ext hx'
  · right
    rw [eq_top_iff, ← hN]
    intro x _
    have hx' : (x : MvPolynomial (Fin 2) k) ∈ M.toSubmodule := by
      rw [htop, Subcomodule.mem_toSubmodule]
      exact x.2
    rw [Subcomodule.map_toSubmodule] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [Subcomodule.subtype_toLinearMap, SMulMemClass.subtype_apply] at hyx
    exact (Subtype.ext hyx : y = x) ▸ hy

/-- Equipping `binaryForms k d` with its differentiated `sl(2, k)`-action, it is an irreducible
`sl(2, k)`-module over an algebraically closed field of characteristic zero. -/
theorem isIrreducible_binaryForms (d : ℕ) :
    LieModule.IsIrreducible k (LieAlgebra.SpecialLinear.sl (Fin 2) k) (binaryForms k d) := by
  have hpos : 0 < Module.finrank k (binaryForms k d) := by
    rw [finrank_binaryForms]
    exact Nat.succ_pos d
  have _ : Nontrivial (binaryForms k d) := Module.nontrivial_of_finrank_pos hpos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbot ↦ ?_⟩, eq_bot_or_eq_top := fun W ↦ ?_ }
  · let _ : Subsingleton (binaryForms k d) :=
      subsingleton_of_forall_eq 0 fun x ↦
        (LieSubmodule.mem_bot _).mp (hbot.symm ▸ LieSubmodule.mem_top x)
    exact false_of_nontrivial_of_subsingleton (binaryForms k d)
  · rw [← LieSubmodule.toSubmodule_inj, ← LieSubmodule.toSubmodule_inj,
      LieSubmodule.bot_toSubmodule, LieSubmodule.top_toSubmodule]
    refine eq_bot_or_eq_top_of_differential_mem_binaryForms d W.toSubmodule fun δ w hw ↦ ?_
    have hmem : ⁅tangentLieEquivSl (R := k) (B := k) 2 δ, w⁆ ∈ W := W.lie_mem hw
    rwa [slLieRingModule_bracket, slDifferential_tangentLieEquivSl] at hmem

/-- Over an algebraically closed field of characteristic zero, the degree-`d` binary forms with
their differentiated `sl(2, k)`-action are isomorphic as an `sl(2, k)`-module to the standard
irreducible module `Sl2Std k d`. -/
theorem nonempty_lieModuleEquiv_binaryForms_sl2Std (d : ℕ) :
    Nonempty (binaryForms k d ≃ₗ⁅k, LieAlgebra.SpecialLinear.sl (Fin 2) k⁆ Sl2Std k d) := by
  have hpos : 0 < Module.finrank k (binaryForms k d) := by
    rw [finrank_binaryForms]
    exact Nat.succ_pos d
  have _ : FiniteDimensional k (binaryForms k d) := Module.finite_of_finrank_pos hpos
  have _ : LieModule.IsIrreducible k (LieAlgebra.SpecialLinear.sl (Fin 2) k) (binaryForms k d) :=
    isIrreducible_binaryForms d
  obtain ⟨n, ⟨e⟩, -⟩ := Sl2Std.existsUnique_nonempty_lieModuleEquiv (K := k) (binaryForms k d)
  have hrank : Module.finrank k (binaryForms k d) = Module.finrank k (Sl2Std k n) :=
    e.toLinearEquiv.finrank_eq
  rw [finrank_binaryForms, Sl2Std.finrank_eq] at hrank
  have hnd : n = d := by omega
  subst hnd
  exact ⟨e⟩

private theorem exists_comodule_of_isIrreducible
    (V : Type w) [AddCommGroup V] [Module k V]
    [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
    [LieModule k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
    [FiniteDimensional k V]
    [LieModule.IsIrreducible k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V] :
    ∃ c : Comodule k (coordinateHopfAlgebra k 2) V,
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (v : V),
        @Comodule.differential k (coordinateHopfAlgebra k 2) V _ _ _ _ _ c d v =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, v⁆ := by
  obtain ⟨d, ⟨e₁⟩, -⟩ := Sl2Std.existsUnique_nonempty_lieModuleEquiv (K := k) V
  obtain ⟨e₂⟩ := nonempty_lieModuleEquiv_binaryForms_sl2Std (k := k) d
  let e : binaryForms k d ≃ₗ⁅k, LieAlgebra.SpecialLinear.sl (Fin 2) k⁆ V := e₂.trans e₁.symm
  refine ⟨Comodule.Transport (C := coordinateHopfAlgebra k 2) e.toLinearEquiv, fun δ v ↦ ?_⟩
  rw [Comodule.differential_transport]
  set w := e.toLinearEquiv.symm v
  have hact :
      Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2)
          (M := binaryForms k d) δ w =
        ⁅tangentLieEquivSl (R := k) (B := k) 2 δ, w⁆ := by
    rw [slLieRingModule_bracket, slDifferential_tangentLieEquivSl]
  rw [hact]
  exact (e.map_lie (tangentLieEquivSl (R := k) (B := k) 2 δ) w).trans
    (congrArg (⁅tangentLieEquivSl (R := k) (B := k) 2 δ, ·⁆)
      (e.toLinearEquiv.apply_symm_apply v))

end BinaryFormsIrreducible

section IntegrateComodule

private theorem exists_comodule_of_lieModule_aux :
    ∀ (r : ℕ) (V : Type w) [AddCommGroup V] [Module k V]
      [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
      [LieModule k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
      [FiniteDimensional k V],
      Module.finrank k V = r →
      ∃ c : Comodule k (coordinateHopfAlgebra k 2) V,
        ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
            (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (v : V),
          @Comodule.differential k (coordinateHopfAlgebra k 2) V _ _ _ _ _ c d v =
            ⁅tangentLieEquivSl (R := k) (B := k) 2 d, v⁆ := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro V _ _ _ _ _ hr
    by_cases hsub : Subsingleton V
    · refine ⟨Comodule.trivial, fun _ _ ↦ ?_⟩
      exact Subsingleton.elim _ _
    · rw [not_subsingleton_iff_nontrivial] at hsub
      by_cases hred :
          ∃ N : LieSubmodule k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V, N ≠ ⊥ ∧ N ≠ ⊤
      · obtain ⟨N, hNbot, hNtop⟩ := hred
        obtain ⟨N', hNN'⟩ := exists_isCompl_sl_fin_two N
        have hN'top : N' ≠ ⊤ := by
          intro htop
          apply hNbot
          rw [eq_bot_iff]
          intro x hx
          have hx' : x ∈ N ⊓ N' := ⟨hx, htop.symm ▸ trivial⟩
          rwa [hNN'.inf_eq_bot, LieSubmodule.mem_bot] at hx'
        have hNtopSub : N.toSubmodule ≠ ⊤ := fun h ↦
          hNtop ((LieSubmodule.toSubmodule_inj _ _).mp
            (h.trans LieSubmodule.top_toSubmodule.symm))
        have hN'topSub : N'.toSubmodule ≠ ⊤ := fun h ↦
          hN'top ((LieSubmodule.toSubmodule_inj _ _).mp
            (h.trans LieSubmodule.top_toSubmodule.symm))
        have hNlt : Module.finrank k N < r := hr ▸ Submodule.finrank_lt hNtopSub
        have hN'lt : Module.finrank k N' < r := hr ▸ Submodule.finrank_lt hN'topSub
        obtain ⟨cN, hcN⟩ := ih (Module.finrank k N) hNlt N rfl
        obtain ⟨cN', hcN'⟩ := ih (Module.finrank k N') hN'lt N' rfl
        let cProd : Comodule k (coordinateHopfAlgebra k 2) (N × N') :=
          @Comodule.Prod k _ (coordinateHopfAlgebra k 2) _ _ _ N N' _ _ cN _ _ cN'
        have hcomplSub : IsCompl N.toSubmodule N'.toSubmodule :=
          LieSubmodule.isCompl_toSubmodule.mpr hNN'
        let e : (N × N') ≃ₗ[k] V :=
          Submodule.prodEquivOfIsCompl N.toSubmodule N'.toSubmodule hcomplSub
        refine ⟨@Comodule.Transport k (coordinateHopfAlgebra k 2) (N × N') V _ _ _ _ _ _
          cProd _ _ e, fun d v ↦ ?_⟩
        rw [@Comodule.differential_transport k (coordinateHopfAlgebra k 2) (N × N') _ _ _ _ _ cProd
          V _ _ e d v,
          @Comodule.differential_prod k (coordinateHopfAlgebra k 2) N _ _ _ _ _ cN N' _ _ cN' d
            (e.symm v),
          hcN, hcN']
        set p := e.symm v
        have hp : e p = v := e.apply_symm_apply v
        have he (x : N × N') : e x = (x.1 : V) + (x.2 : V) :=
          Submodule.coe_prodEquivOfIsCompl' N.toSubmodule N'.toSubmodule hcomplSub x
        rw [he, LieSubmodule.coe_bracket, LieSubmodule.coe_bracket, ← lie_add, ← he p, hp]
      · push Not at hred
        have _ : LieModule.IsIrreducible k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V :=
          { exists_pair_ne := ⟨⊥, ⊤, fun hbot ↦ by
              let _ : Subsingleton V :=
                subsingleton_of_forall_eq 0 fun x ↦
                  (LieSubmodule.mem_bot _).mp (hbot.symm ▸ LieSubmodule.mem_top x)
              exact false_of_nontrivial_of_subsingleton V⟩
            eq_bot_or_eq_top := fun N ↦ by
              by_cases hN : N = ⊥
              · exact Or.inl hN
              · exact Or.inr (hred N hN) }
        exact exists_comodule_of_isIrreducible V

/-- **Every finite-dimensional `sl(2, k)`-module integrates uniquely to `SL₂`** over an
algebraically closed field of characteristic zero: there is a unique comodule structure on `V`
over `O(SL₂)` whose differentiated action agrees with the given `sl(2, k)`-action. -/
theorem existsUnique_comodule_of_lieModule
    (V : Type w) [AddCommGroup V] [Module k V]
    [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
    [LieModule k (LieAlgebra.SpecialLinear.sl (Fin 2) k) V]
    [FiniteDimensional k V] :
    ∃! c : Comodule k (coordinateHopfAlgebra k 2) V,
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (v : V),
        @Comodule.differential k (coordinateHopfAlgebra k 2) V _ _ _ _ _ c d v =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, v⁆ := by
  obtain ⟨c, hc⟩ := exists_comodule_of_lieModule_aux (Module.finrank k V) V rfl
  refine ⟨c, hc, fun c' hc' ↦ ?_⟩
  exact Comodule.ext_of_differential_eq
    (H := FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k 2))
    c' c fun d v ↦ (hc' d v).trans (hc d v).symm

end IntegrateComodule

/-! ### Integrating Lie homomorphisms `sl(2, k) → Lie(G)` to `SL₂ → G` -/

section IntegrateHom

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- Every Lie algebra homomorphism `φ : sl(2, k) →ₗ⁅k⁆ Lie(Spec H)` into the tangent Lie algebra
of a finite-type commutative Hopf algebra over an algebraically closed field of characteristic zero
comes from a unique bialgebra morphism `H →ₐc[k] O(SL₂)`. -/
theorem existsUnique_bialgHom_derivationCompLieHom_eq
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∃! f : H →ₐc[k] coordinateHopfAlgebra k 2,
      derivationCompLieHom (B := k) f =
        φ.comp (tangentLieEquivSl (R := k) (B := k) 2).toLieHom := by
  obtain ⟨M, n, b, hb⟩ := Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  have _ : FiniteDimensional k M := Module.Finite.of_basis b
  let _ : LieRing (Module.End k M) := LieRing.ofAssociativeRing
  let ρLie : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆ Module.End k M :=
    (Comodule.differential (R := k) (H := H) (M := M)).comp φ
  let _ : LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) k) M :=
    LieRingModule.compLieHom M ρLie
  let _ : LieModule k (LieAlgebra.SpecialLinear.sl (Fin 2) k) M :=
    LieModule.compLieHom M ρLie
  obtain ⟨cK, hcK, -⟩ := existsUnique_comodule_of_lieModule (k := k) M
  refine CommHopfAlgCat.existsUnique_bialgHom_derivationCompLieHom_eq_of_surjective
    (K := FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k 2))
    (φ.comp (tangentLieEquivSl (R := k) (B := k) 2).toLieHom) b hb cK fun d m ↦ ?_
  exact hcK d m

/-- **Integration of Lie homomorphisms from `sl(2, k)`.** Given a finite-type commutative Hopf
algebra `H` over an algebraically closed field `k` of characteristic zero and a Lie algebra
homomorphism `φ : sl(2, k) →ₗ⁅k⁆ Lie(Spec H)`, `integrateLieHom φ` is the unique bialgebra
morphism `H →ₐc[k] O(SL₂)` whose differential at the identity is `φ`. -/
noncomputable def integrateLieHom
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    H →ₐc[k] coordinateHopfAlgebra k 2 :=
  (existsUnique_bialgHom_derivationCompLieHom_eq φ).choose

/-- The differential of `integrateLieHom φ` as a Lie homomorphism on `Lie(SL₂)` is `φ` composed
with `tangentLieEquivSl 2`. -/
@[simp]
theorem derivationCompLieHom_integrateLieHom
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    derivationCompLieHom (B := k) (integrateLieHom φ) =
      φ.comp (tangentLieEquivSl (R := k) (B := k) 2).toLieHom :=
  (existsUnique_bialgHom_derivationCompLieHom_eq φ).choose_spec.1

/-- Evaluating the differential of `integrateLieHom φ` on a tangent derivation `d` of `SL₂` gives
`φ (tangentLieEquivSl 2 d)`. -/
@[simp]
theorem derivationComp_integrateLieHom
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k))
    (d : Derivation k (coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) :
    derivationComp (integrateLieHom φ) d = φ (tangentLieEquivSl (R := k) (B := k) 2 d) := by
  simpa only [derivationCompLieHom_apply, LieHom.comp_apply, LieEquiv.coe_toLieHom] using
    DFunLike.congr_fun (derivationCompLieHom_integrateLieHom φ) d

/-- Evaluating the differential of `integrateLieHom φ` on `(tangentLieEquivSl 2).symm X` recovers
`φ X`. -/
@[simp]
theorem derivationComp_integrateLieHom_symm
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k))
    (X : LieAlgebra.SpecialLinear.sl (Fin 2) k) :
    derivationComp (integrateLieHom φ) ((tangentLieEquivSl (R := k) (B := k) 2).symm X) = φ X := by
  rw [derivationComp_integrateLieHom, LieEquiv.apply_symm_apply]

/-- A bialgebra morphism `f : H →ₐc[k] O(SL₂)` equals `integrateLieHom φ` if and only if its
differential is `φ ∘ tangentLieEquivSl 2`. -/
theorem eq_integrateLieHom_iff
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k))
    (f : H →ₐc[k] coordinateHopfAlgebra k 2) :
    f = integrateLieHom φ ↔
      derivationCompLieHom (B := k) f =
        φ.comp (tangentLieEquivSl (R := k) (B := k) 2).toLieHom :=
  ⟨fun h ↦ h ▸ derivationCompLieHom_integrateLieHom φ,
    (existsUnique_bialgHom_derivationCompLieHom_eq φ).choose_spec.2 f⟩

/-- Integrating the zero Lie homomorphism gives the trivial group homomorphism. -/
@[simp]
theorem integrateLieHom_zero :
    integrateLieHom (0 : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)) =
      (Bialgebra.unitBialgHom k (coordinateHopfAlgebra k 2)).comp
        (Bialgebra.counitBialgHom k H) := by
  symm
  rw [eq_integrateLieHom_iff]
  ext d a
  simp [derivationCompLieHom_apply, derivationComp_apply, Bialgebra.unitBialgHom]
  rfl

/-- Integrating `(tangentLieEquivSl 2).symm` recovers the identity on `O(SL₂)`. -/
@[simp]
theorem integrateLieHom_tangentLieEquivSl_symm :
    integrateLieHom (tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom =
      BialgHom.id k (coordinateHopfAlgebra k 2) := by
  symm
  rw [eq_integrateLieHom_iff]
  ext d
  simp

/-- Naturality of `integrateLieHom` with respect to group homomorphisms `Spec H → Spec H'`. -/
theorem integrateLieHom_comp {H' : Type u} [CommRing H'] [HopfAlgebra k H']
    [Algebra.FiniteType k H'] (ψ : H' →ₐc[k] H)
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    (integrateLieHom φ).comp ψ =
      integrateLieHom ((derivationCompLieHom (B := k) ψ).comp φ) := by
  rw [eq_integrateLieHom_iff, derivationCompLieHom_comp, derivationCompLieHom_integrateLieHom]
  ext d
  rfl

/-! ### Centrality and `{±I}` structure of the kernel for injective `φ` -/

/-- When `φ` is injective, the scheme-theoretic kernel of `integrateLieHom φ` has zero Lie
algebra. -/
theorem lieSubalgebra_kernelHopfIdeal_integrateLieHom
    {φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hφ : Function.Injective φ) :
    (CommHopfAlgCat.kernelHopfIdeal
      (_root_.CommHopfAlgCat.ofHom (integrateLieHom φ))).lieSubalgebra (B := k) = ⊥ := by
  rw [CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal, eq_bot_iff]
  intro d hd
  rw [LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker, _root_.CommHopfAlgCat.hom_ofHom,
    derivationCompLieHom_integrateLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom] at hd
  have h0 : tangentLieEquivSl (R := k) (B := k) 2 d = 0 := hφ (hd.trans (map_zero φ).symm)
  exact (tangentLieEquivSl (R := k) (B := k) 2).injective (h0.trans (map_zero _).symm)

/-- When `φ` is injective, the scheme-theoretic kernel of `integrateLieHom φ` is a central closed
subgroup of `SL₂`. -/
theorem isCentral_kernelHopfIdeal_integrateLieHom
    {φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hφ : Function.Injective φ) :
    (CommHopfAlgCat.kernelHopfIdeal
      (_root_.CommHopfAlgCat.ofHom (integrateLieHom φ))).IsCentral := by
  let K₂ := FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k 2)
  let f : _root_.CommHopfAlgCat.of k H ⟶ K₂.obj :=
    _root_.CommHopfAlgCat.ofHom (integrateLieHom φ)
  let I : HopfIdeal k K₂ := CommHopfAlgCat.kernelHopfIdeal f
  let Q := FiniteTypeCommHopfAlgCat.quotient K₂ I
  have hlie : I.lieSubalgebra (B := k) = ⊥ := lieSubalgebra_kernelHopfIdeal_integrateLieHom hφ
  let _ : Subsingleton (I.lieSubalgebra (B := k)) :=
    subsingleton_of_forall_eq 0 fun a ↦ Subtype.ext <| by
      let a₀ : Derivation k K₂ (Bialgebra.CounitAlgebra k K₂ k) := a.1
      have ha : a₀ ∈ I.lieSubalgebra (B := k) := a.2
      rw [hlie, LieSubalgebra.mem_bot] at ha
      exact ha
  have hfinrank : Module.finrank k (Derivation k Q (Bialgebra.CounitAlgebra k Q k)) = 0 := by
    rw [(HopfIdeal.quotientLieEquiv (B := k) I).toLinearEquiv.finrank_eq]
    exact Module.finrank_zero_of_subsingleton
  have hid :=
    FiniteTypeCommHopfAlgCat.identityComponentHopfIdeal_eq_augmentation_of_finrank_lie_eq_zero
      Q hfinrank
  let _ : Module.Finite k (CommHopfAlgCat.quotient K₂.obj I) :=
    FiniteTypeCommHopfAlgCat.moduleFinite_of_identityComponentHopfIdeal_eq_augmentation Q hid
  let _ : Algebra.Smooth k K₂.obj :=
    (smoothCommHopfAlgProperty_iff K₂.obj).mp (smoothCommHopfAlgProperty_of_charZero k K₂.obj)
  let _ : IsReduced K₂.obj := isReduced_of_smooth k K₂.obj
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient K₂.obj I) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k (CommHopfAlgCat.quotient K₂.obj I))
  let _ : IsReduced (CommHopfAlgCat.quotient K₂.obj I) :=
    isReduced_of_smooth k (CommHopfAlgCat.quotient K₂.obj I)
  exact (CommHopfAlgCat.isNormal_kernelHopfIdeal f).isCentral_of_finite_of_isReduced
    (H := K₂.obj)

/-- When `φ` is injective, the scheme-theoretic kernel of `integrateLieHom φ` is contained in the
scheme-theoretic center `Z(SL₂) = μ₂` (contravariantly, `centerDefiningIdeal ≤ kernelHopfIdeal`). -/
theorem centerDefiningIdeal_le_kernelHopfIdeal_integrateLieHom
    {φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hφ : Function.Injective φ) :
    CommHopfAlgCat.centerDefiningIdeal (_root_.CommHopfAlgCat.of k (coordinateHopfAlgebra k 2)) ≤
      CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom (integrateLieHom φ)) :=
  (CommHopfAlgCat.centerDefiningIdeal_le_iff _ _).mpr
    (isCentral_kernelHopfIdeal_integrateLieHom hφ)

/-- Over any integral domain `A` over `k` (in particular `A = k`), every `A`-point of `SL₂` in the
kernel of `integrateLieHom φ` for injective `φ` has matrix `1` or `-1` in `SL(2, A)`. -/
theorem pointsMulEquiv_eq_one_or_neg_one_of_mem_kernel_integrateLieHom
    {φ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hφ : Function.Injective φ)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
    (g : WithConv (coordinateHopfAlgebra k 2 →ₐ[k] A))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k (coordinateHopfAlgebra k 2))
      (CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom (integrateLieHom φ)))
      (CommAlgCat.of k A)) :
    pointsMulEquiv (R := k) (A := A) 2 g = 1 ∨
      pointsMulEquiv (R := k) (A := A) 2 g = -1 := by
  have hcenter : g ∈ CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k 2)
      (CommAlgCat.of k A) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
    exact fun x hx ↦ hg x (centerDefiningIdeal_le_kernelHopfIdeal_integrateLieHom hφ hx)
  let r := (rootsOfUnityScalarCenterIso (k := k) 2 zero_lt_two (CommAlgCat.of k A)).inv
    ⟨g, hcenter⟩
  have hgr : rootsOfUnityScalarPoints 2 r = g := by
    have hinv := congrArg Subtype.val
      ((rootsOfUnityScalarCenterIso (k := k) 2 zero_lt_two (CommAlgCat.of k A)).inv_hom_id_apply
        ⟨g, hcenter⟩)
    exact (rootsOfUnityScalarCenterIso_hom_apply (k := k) 2 zero_lt_two
      (CommAlgCat.of k A) r).symm.trans hinv
  let ζ := RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) 2 r
  have hζ : (ζ.1 : Aˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 ζ.1).mp ζ.2
  have hζsq : ((ζ : Aˣ) : A) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  rcases sq_eq_one_iff.mp hζsq with h1 | hm1
  · left
    apply Subtype.ext
    rw [← hgr, coe_pointsMulEquiv_rootsOfUnityScalarPoints, h1, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [← hgr, coe_pointsMulEquiv_rootsOfUnityScalarPoints, hm1, map_neg, map_one,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

end IntegrateHom

end AlgClosedCharZero

end SpecialLinear

end TauCeti
