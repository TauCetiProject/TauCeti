/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# The coefficient pairing of trivial `𝔽₂` coefficients

Multiplication in `𝔽₂` is a `G`-equivariant biadditive map of the lifted carrier of the trivial
`𝔽₂` coefficient object (`TauCeti.trivialF2Pairing`). This file reads it as a coefficient pairing
`TauCeti.TopPairing` of `TauCeti.trivialF2` itself, which is what the `𝔽₂`-valued cup products of
continuous cohomology are formed from. It is the `ℤ`-coefficient counterpart of
`TauCeti.fpPairing`, whose coefficient object `TauCeti.trivialFp` is a `ZMod p`-module.

## Main definitions

* `TauCeti.trivialF2TopPairing`: multiplication on the trivial integral `𝔽₂` coefficient object.

## Main results

* `TauCeti.trivialF2TopPairing_bil_apply`: the pairing multiplies the underlying values in
  `ZMod 2`.
* `TauCeti.trivialF2TopPairing_flip`: the opposite of the multiplication pairing is itself.
* `TauCeti.trivialF2Map_cup`: pullback preserves cup products with trivial `𝔽₂` coefficients.
* `TauCeti.trivialF2TopPairing_cup_one_one_explicitH1`: on explicit cocycles, the cup product of
  two classes of `H¹(G, 𝔽₂)` is the class of the product cocycle `(g, h) ↦ a g * b h`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (G : Type u) [Monoid G]

attribute [local instance] TopRep.distribMulAction

/-- Multiplication on the trivial `𝔽₂` coefficient object, as a continuous equivariant pairing
over `ℤ`. It is the generic discrete-module pairing `TauCeti.ofDiscreteModulePairing` of
`TauCeti.trivialF2Pairing`, read on the coefficient object itself along
`TauCeti.ofDiscreteModule_trivialF2`. This is the coefficient pairing used by the mod-two Kummer
cup. -/
noncomputable def trivialF2TopPairing :
    TopPairing (trivialF2 G) (trivialF2 G) (trivialF2 G) :=
  cast (congrArg (fun X ↦ TopPairing X X X) (ofDiscreteModule_trivialF2 G))
    (ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G))

/-- The coefficient pairing multiplies the underlying values in `ZMod 2`. -/
@[simp]
theorem trivialF2TopPairing_bil_apply (x y : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x y =
      (trivialF2Equiv G).symm (trivialF2Equiv G x * trivialF2Equiv G y) := by
  rw [trivialF2TopPairing, TopPairing.bil_transport _ (ofDiscreteModule_trivialF2 G)
      (ofDiscreteModule_trivialF2 G) (ofDiscreteModule_trivialF2 G),
    eqToHom_ofDiscreteModule_trivialF2_symm_apply,
    eqToHom_ofDiscreteModule_trivialF2_symm_apply, ofDiscreteModulePairing_bil_apply,
    eqToHom_ofDiscreteModule_trivialF2_apply, trivialF2Pairing_apply]

/-- Multiplication on the trivial `𝔽₂` coefficient object is symmetric. -/
theorem trivialF2TopPairing_bil_comm (x y : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x y = (trivialF2TopPairing G).bil y x := by
  simp only [trivialF2TopPairing_bil_apply, mul_comm]

/-- The opposite of the multiplication pairing is itself, because multiplication in `ZMod 2` is
commutative. -/
@[simp]
theorem trivialF2TopPairing_flip : (trivialF2TopPairing G).flip = trivialF2TopPairing G :=
  -- `DFunLike.ext` rather than `LinearMap.ext₂`: the latter would synthesize the `ℤ`-module
  -- structure on the carrier as `AddCommGroup.toIntModule`, not the coefficient object's own.
  TopPairing.ext (DFunLike.ext _ _ fun x ↦ DFunLike.ext _ _ fun y ↦ by
    rw [TopPairing.flip_bil, trivialF2TopPairing_bil_comm])

/-- Pullback with trivial `𝔽₂` coefficients preserves the cup product in every bidegree. -/
@[simp]
theorem trivialF2Map_cup {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (φ : H →ₜ* G) (m n : ℕ)
    (x : continuousCohomology m (trivialF2 G))
    (y : continuousCohomology n (trivialF2 G)) :
    trivialF2Map φ (m + n) ((trivialF2TopPairing G).cup m n x y) =
      (trivialF2TopPairing H).cup m n (trivialF2Map φ m x) (trivialF2Map φ n y) := by
  simp only [trivialF2Map_def]
  apply (trivialF2TopPairing G).cup_map (trivialF2TopPairing H)
  intro a b
  apply (trivialF2Equiv H).injective
  rw [TopRep.eqToHom_hom_apply (res_trivialF2_hom φ)]
  simp only [trivialF2TopPairing_bil_apply, TopRep.eqToHom_hom_apply (res_trivialF2_hom φ),
    trivialF2Equiv_cast, AddEquiv.apply_symm_apply]

end TauCeti

/-! ### The cup product on explicit cocycles -/

namespace TauCeti

open CategoryTheory ContCohomology _root_.ContinuousCohomology

universe u

attribute [local instance] TopRep.distribMulAction

variable (G : Type u) [Group G]

/-- The transport along `ofDiscreteModule_trivialF2` intertwines multiplication on the discrete
module `𝔽₂` with the coefficient pairing `trivialF2TopPairing`. -/
private theorem eqToHom_ofDiscreteModulePairing_bil (x y : (trivialF2 G).V) :
    eqToHom (ofDiscreteModule_trivialF2 G)
        ((ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)).bil x y) =
      (trivialF2TopPairing G).bil (eqToHom (ofDiscreteModule_trivialF2 G) x)
        (eqToHom (ofDiscreteModule_trivialF2 G) y) := by
  rw [ofDiscreteModulePairing_bil_apply, eqToHom_ofDiscreteModule_trivialF2_apply,
    eqToHom_ofDiscreteModule_trivialF2_apply, eqToHom_ofDiscreteModule_trivialF2_apply,
    trivialF2TopPairing_bil_apply, trivialF2Pairing_apply]

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- **The cup product of two classes of `H¹(G, 𝔽₂)` on explicit cocycles.** For explicit classes
`x` and `y`, read in `H¹(G, 𝔽₂)` through the comparison with continuous cohomology and the
transport `ofDiscreteModule_trivialF2`, their cup product along `trivialF2TopPairing` is the
explicit `(1, 1)` cup product of multiplication in `𝔽₂`, `(a ⌣ b) (g, h) = a g * b h`, read in
`H²(G, 𝔽₂)` the same way. -/
theorem trivialF2TopPairing_cup_one_one_explicitH1 (x y : H1 G (trivialF2 G).V) :
    (trivialF2TopPairing G).cup 1 1
      ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
        (explicitH1AddEquivContinuousCohomology G _ x))
      ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
        (explicitH1AddEquivContinuousCohomology G _ y)) =
    (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom
      (explicitH2AddEquivContinuousCohomology G _
        (explicitCup11 G _ _ _ (trivialF2Pairing G) continuous_of_discreteTopology
          (trivialF2Pairing_smul_smul G) x y)) := by
  -- naturality of the cup product along the transport `ofDiscreteModule_trivialF2`, read on the
  -- explicit cup product through `explicitAddEquiv_cup11`
  have key := (ofDiscreteModulePairing (trivialF2Pairing G)
    (trivialF2Pairing_smul_smul G)).cup_coeffMap (trivialF2TopPairing G)
    (eqToHom (ofDiscreteModule_trivialF2 G)) (eqToHom (ofDiscreteModule_trivialF2 G))
    (eqToHom (ofDiscreteModule_trivialF2 G)) (eqToHom_ofDiscreteModulePairing_bil G) 1 1
    (explicitH1AddEquivContinuousCohomology G _ x) (explicitH1AddEquivContinuousCohomology G _ y)
  rw [explicitAddEquiv_cup11, TauCeti.ContinuousCohomology.coeffMap_eqToHom,
    TauCeti.ContinuousCohomology.coeffMap_eqToHom] at key
  -- `key` is the statement up to the spelling of the degree, `1 + 1` rather than `2`, and of the
  -- application of morphisms of topological modules
  convert key.symm using 2

end TauCeti
