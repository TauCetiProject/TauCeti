/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Kaehler.Trace.Basic
public import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Functoriality of the trace of differentials

The trace derivation commutes with compatible maps of finite free algebras that take a basis
to a basis (`Derivation.traceDeriv_map`), and with postcomposition of the original derivation by
a linear map (`Derivation.traceDeriv_compDer`). The two derivations may have different
constant rings. This compatibility extends from individual differential generators to the full
Kähler differential pairing (`Derivation.liftKaehlerDifferential_traceDerivation_map`) and its
trace (`Derivation.traceLin_map`). These are the naturality identities used in localization
and coefficient-extension arguments.

-/

public section

open Algebra TauCeti.Algebra

namespace Derivation

variable {k k' R B M R' B' M' : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)
  [CommRing k'] [CommRing R'] [CommRing B'] [Algebra k' R'] [Algebra R' B']
  [AddCommGroup M'] [Module R' M']
  [Module k' M'] (D' : Derivation k' R' M')

variable [Module.Free R B] [Module.Finite R B] [Module.Free R' B'] [Module.Finite R' B']

/-- **Functoriality of the trace derivation.** Let `σ : R → R'`, `ψ : B → B'` and `μ : M → M'`
be compatible maps such that `ψ` maps a basis of `B` over `R` to a basis of `B'` over `R'`, and
`D' ∘ σ = μ ∘ D`. Then `traceDeriv D' (ψ a) (ψ c) = μ (traceDeriv D a c)`. -/
lemma traceDeriv_map {ι : Type*} (b : Module.Basis ι R B)
    (b' : Module.Basis ι R' B') (σ : R →+* R') (ψ : B →+* B')
    (hψ : ∀ r, ψ (algebraMap R B r) = algebraMap R' B' (σ r)) (hb : ∀ i, b' i = ψ (b i))
    (μ : M →+ M') (hμ : ∀ (r : R) (m : M), μ (r • m) = σ r • μ m)
    (hD : ∀ r, D' (σ r) = μ (D r)) (a c : B) :
    traceDeriv D' (ψ a) (ψ c) = μ (traceDeriv D a c) := by
  classical
  cases subsingleton_or_nontrivial R' with
  | inl h =>
    have : Subsingleton M' := Module.subsingleton R' M'
    exact Subsingleton.elim _ _
  | inr h =>
    have := Module.Finite.finite_basis b'
    have := Fintype.ofFinite ι
    rw [traceDeriv_eq D' b', traceDeriv_eq D b, traceDerivOfBasis_def, traceDerivOfBasis_def,
      leftMulMatrix_map b b' σ ψ hψ hb, leftMulMatrix_map b b' σ ψ hψ hb]
    simp only [Derivation.traceDerivForm_def, Matrix.map_apply, map_sum, hμ, hD]

end Derivation

namespace Derivation

variable {k k' R R' B B' M M' : Type*}
  [CommRing k] [CommRing k'] [Algebra k k'] [CommRing R] [CommRing R']
  [Algebra k R] [Algebra k' R'] [Algebra R R']
  [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B']
  [Algebra k B] [IsScalarTower k R B]
  [Algebra k' B'] [IsScalarTower k' R' B']
  [Algebra B B'] [Algebra k B'] [IsScalarTower k B B'] [IsScalarTower k k' B']
  [Algebra R B'] [IsScalarTower R B B'] [IsScalarTower R R' B']
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup M'] [Module R' M'] [Module k' M'] [IsScalarTower k' R' M']
  [Module.Free R B] [Module.Finite R B] [Module.Free R' B'] [Module.Finite R' B']
  (D : Derivation k R M) (D' : Derivation k' R' M')

/-- The differential trace pairing commutes with a compatible coefficient map. The algebra
map must carry a basis to a basis; the constant rings of the derivations may differ. -/
lemma liftKaehlerDifferential_traceDerivation_map {ι : Type*}
    (b : Module.Basis ι R B) (b' : Module.Basis ι R' B')
    (hb : ∀ i, b' i = algebraMap B B' (b i))
    (μ : M →ₛₗ[algebraMap R R'] M') (hD : ∀ r, D' (algebraMap R R' r) = μ (D r))
    (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B') D').liftKaehlerDifferential
        (KaehlerDifferential.map k k' B B' ω) (algebraMap B B' c) =
      μ ((traceDerivation (B := B) D).liftKaehlerDifferential ω c) := by
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [KaehlerDifferential.map_D, liftKaehlerDifferential_comp_D,
      liftKaehlerDifferential_comp_D, traceDerivation_apply, traceDerivation_apply]
    exact traceDeriv_map D D' b b' (algebraMap R R') (algebraMap B B')
      (fun r ↦ (IsScalarTower.algebraMap_apply R B B' r).symm.trans
        (IsScalarTower.algebraMap_apply R R' B' r)) hb μ.toAddMonoidHom
      (fun r m ↦ μ.map_smulₛₗ r m) hD a c
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, PrecompLinearMap.add_apply, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, PrecompLinearMap.smul_apply,
      ← algebraMap_smul B' a, LinearMap.map_smul, PrecompLinearMap.smul_apply,
      Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, ← map_mul, smul_eq_mul]
    exact hx (a * c)

/-- The trace on Kähler differentials commutes with a semilinear map intertwining the
derivations, when the algebra map carries the displayed basis to the target basis. -/
lemma traceLin_map {ι : Type*}
    (b : Module.Basis ι R B) (b' : Module.Basis ι R' B')
    (hb : ∀ i, b' i = algebraMap B B' (b i))
    (μ : M →ₛₗ[algebraMap R R'] M') (hD : ∀ r, D' (algebraMap R R' r) = μ (D r))
    (ω : Ω[B⁄k]) :
    traceLin D' (KaehlerDifferential.map k k' B B' ω) = μ (traceLin D ω) := by
  simpa only [traceLin_apply, map_one] using
    liftKaehlerDifferential_traceDerivation_map D D' b b' hb μ hD ω 1

/-- The universal differential trace pairing commutes with changes of constant and base
rings when the algebra map carries the displayed basis to the target basis. -/
lemma liftKaehlerDifferential_traceDerivation_D_map
    [Algebra k R'] [IsScalarTower k R R'] [IsScalarTower k k' R']
    {ι : Type*} (b : Module.Basis ι R B) (b' : Module.Basis ι R' B')
    (hb : ∀ i, b' i = algebraMap B B' (b i)) (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B') (KaehlerDifferential.D k' R')).liftKaehlerDifferential
        (KaehlerDifferential.map k k' B B' ω) (algebraMap B B' c) =
      KaehlerDifferential.map k k' R R'
        ((traceDerivation (B := B) (KaehlerDifferential.D k R)).liftKaehlerDifferential ω c) := by
  let μ : Ω[R⁄k] →ₛₗ[algebraMap R R'] Ω[R'⁄k'] :=
    { toFun := KaehlerDifferential.map k k' R R'
      map_add' := map_add _
      map_smul' r x := by
        rw [LinearMap.map_smul]
        exact (algebraMap_smul R' r ((KaehlerDifferential.map k k' R R') x)).symm }
  exact liftKaehlerDifferential_traceDerivation_map
    (KaehlerDifferential.D k R) (KaehlerDifferential.D k' R') b b' hb μ
    (fun r ↦ (KaehlerDifferential.map_D k k' R R' r).symm) ω c

/-- The universal differential trace commutes with changes of constant and base rings
when the algebra map carries the displayed basis to the target basis. -/
lemma traceLin_D_map
    [Algebra k R'] [IsScalarTower k R R'] [IsScalarTower k k' R']
    {ι : Type*} (b : Module.Basis ι R B) (b' : Module.Basis ι R' B')
    (hb : ∀ i, b' i = algebraMap B B' (b i)) (ω : Ω[B⁄k]) :
    traceLin (B := B') (KaehlerDifferential.D k' R')
        (KaehlerDifferential.map k k' B B' ω) =
      KaehlerDifferential.map k k' R R'
        (traceLin (B := B) (KaehlerDifferential.D k R) ω) := by
  simpa only [traceLin_apply, map_one] using
    liftKaehlerDifferential_traceDerivation_D_map b b' hb ω 1

end Derivation

namespace Derivation

variable {k R B M M' : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)
  [AddCommGroup M'] [Module R M'] [Module k M'] [Module.Free R B] [Module.Finite R B]

/-- The trace derivation is compatible with composition of `D` with a linear map. -/
@[simp]
lemma traceDeriv_compDer [IsScalarTower k R M] [IsScalarTower k R M'] (μ : M →ₗ[R] M')
    (a c : B) : traceDeriv (μ.compDer D) a c = μ (traceDeriv D a c) :=
  traceDeriv_map D (μ.compDer D) (Module.Free.chooseBasis R B) (Module.Free.chooseBasis R B)
    (RingHom.id R) (RingHom.id B) (fun _ ↦ rfl) (fun _ ↦ rfl) μ.toAddMonoidHom
    (fun r m ↦ μ.map_smul r m) (fun _ ↦ rfl) a c


variable [Algebra k B] [IsScalarTower k R B]

/-- Postcomposing the original derivation postcomposes the full differential trace pairing. -/
@[simp]
lemma liftKaehlerDifferential_traceDerivation_compDer
    [IsScalarTower k R M] [IsScalarTower k R M'] (μ : M →ₗ[R] M')
    (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B) (μ.compDer D)).liftKaehlerDifferential ω c =
      μ ((traceDerivation (B := B) D).liftKaehlerDifferential ω c) := by
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp only [liftKaehlerDifferential_comp_D, traceDerivation_apply, traceDeriv_compDer]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, PrecompLinearMap.add_apply, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, PrecompLinearMap.smul_apply,
      PrecompLinearMap.smul_apply]
    exact hx (a * c)

/-- The trace on differentials commutes with postcomposition by a linear coefficient map. -/
lemma traceLin_compDer [IsScalarTower k R M] [IsScalarTower k R M'] (μ : M →ₗ[R] M') :
    traceLin (B := B) (μ.compDer D) = μ ∘ₗ traceLin (B := B) D := by
  apply LinearMap.ext
  intro ω
  simp only [traceLin_apply, LinearMap.comp_apply,
    liftKaehlerDifferential_traceDerivation_compDer]

/-- Evaluation form of compatibility of the differential trace with a linear coefficient map. -/
@[simp]
lemma traceLin_compDer_apply [IsScalarTower k R M] [IsScalarTower k R M'] (μ : M →ₗ[R] M')
    (ω : Ω[B⁄k]) : traceLin (B := B) (μ.compDer D) ω = μ (traceLin (B := B) D ω) := by
  rw [traceLin_compDer, LinearMap.comp_apply]

end Derivation
